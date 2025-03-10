(******************************************************************************)
(*                                ASLRef                                      *)
(******************************************************************************)
(*
 * SPDX-FileCopyrightText: Copyright 2022-2023 Arm Limited and/or its affiliates <open-source-office@arm.com>
 * SPDX-License-Identifier: BSD-3-Clause
 *)
(******************************************************************************)
(* Disclaimer:                                                                *)
(* This material covers both ASLv0 (viz, the existing ASL pseudocode language *)
(* which appears in the Arm Architecture Reference Manual) and ASLv1, a new,  *)
(* experimental, and as yet unreleased version of ASL.                        *)
(* This material is work in progress, more precisely at pre-Alpha quality as  *)
(* per Arm’s quality standards.                                               *)
(* In particular, this means that it would be premature to base any           *)
(* production tool development on this material.                              *)
(* However, any feedback, question, query and feature request would be most   *)
(* welcome; those can be sent to Arm’s Architecture Formal Team Lead          *)
(* Jade Alglave <jade.alglave@arm.com>, or by raising issues or PRs to the    *)
(* herdtools7 github repository.                                              *)
(******************************************************************************)

open AST
open ASTUtils

let desugar_setter call fields rhs =
  let loc = to_pos call and { desc = { name; params; args } } = call in
  let () = assert (loc.version = V1) in
  let here desc = add_pos_from loc desc in
  match fields with
  | [] ->
      (* Setter(rhs, ...); *)
      S_Call { name; args = rhs :: args; params; call_type = ST_Setter }
  | _ ->
      let temp = fresh_var "__setter_v1_temporary" in
      (* temp = Getter(...); *)
      let read =
        let getter_call =
          E_Call { name; args; params; call_type = ST_Getter } |> here
        in
        S_Decl (LDK_Var, LDI_Var temp, None, Some getter_call) |> here
      in
      (* temp.field = rhs OR temp.[field1, field2, ...] = rhs; *)
      let modify =
        let temp_le = LE_Var temp |> here in
        let lhs =
          match fields with
          | [ field ] -> LE_SetField (temp_le, field)
          | _ -> LE_SetFields (temp_le, fields, [])
        in
        S_Assign (lhs |> here, rhs) |> here
      in
      (* Setter(rhs, ...); *)
      let write =
        let temp_e = E_Var temp |> here in
        S_Call { name; args = temp_e :: args; params; call_type = ST_Setter }
        |> here
      in
      S_Seq (s_then read modify, write)

let desugar_elided_parameter ldk lhs ty (call : call annotated) =
  let bits_e =
    match ty.desc with
    | T_Bits (bits_e, []) -> bits_e
    | _ ->
        (* For example, let x = foo{,M}(args); cannot be desugared as there is
           no bits(_) annotation on the left-hand side *)
        Error.fatal_from (to_pos call) CannotParse
  in
  let params = bits_e :: call.desc.params in
  let rhs = E_Call { call.desc with params } |> add_pos_from call in
  S_Decl (ldk, lhs, Some ty, Some rhs)

(* -------------------------------------------------------------------------
    Left-hand sides
   ------------------------------------------------------------------------- *)

type lhs_field = identifier annotated

type lhs_access = {
  base : identifier annotated;
  index : expr option;
  fields : lhs_field list;  (** empty means no fields *)
  slices : slice list annotated;  (** empty means no slices*)
}

let desugar_lhs_access { base; index; fields; slices } =
  let var = LE_Var base.desc |> add_pos_from base in
  let with_index =
    match index with
    | None -> var
    | Some idx -> LE_SetArray (var, idx) |> add_pos_from idx
  in
  let with_fields =
    List.fold_left
      (fun acc field -> LE_SetField (acc, field.desc) |> add_pos_from field)
      with_index fields
  in
  let with_slices =
    match slices.desc with
    | [] -> with_fields
    | _ -> LE_Slice (with_fields, slices.desc) |> add_pos_from slices
  in
  with_slices

let desugar_lhs_tuple laccess_opts =
  let bases =
    List.filter_map (Option.map (fun { base } -> base.desc)) laccess_opts.desc
  in
  match get_first_duplicate bases with
  | Some dup -> Error.fatal_from (to_pos laccess_opts) (MultipleWrites dup)
  | None ->
      let desugar_one = function
        | None -> LE_Discard |> add_pos_from laccess_opts
        | Some laccess -> desugar_lhs_access laccess
      in
      LE_Destructuring (List.map desugar_one laccess_opts.desc)
      |> add_pos_from laccess_opts

let desugar_lhs_fields_tuple base field_opts =
  let fields = List.filter_map (Option.map (fun fld -> fld.desc)) field_opts in
  match get_first_duplicate fields with
  | Some dup ->
      Error.fatal_from (to_pos base) (MultipleWrites (base.desc ^ "." ^ dup))
  | None ->
      let desugar_one = function
        | None -> LE_Discard |> add_pos_from base
        | Some fld ->
            let var = LE_Var base.desc |> add_pos_from base in
            LE_SetField (var, fld.desc) |> add_pos_from fld
      in
      LE_Destructuring (List.map desugar_one field_opts)

let desugar_case_stmt e0 cases otherwise =
  (* Begin CaseToCond *)
  let case_to_cond e0 case tail =
    let { pattern; where; stmt } = case.desc in
    let e_pattern = E_Pattern (e0, pattern) |> add_pos_from pattern in
    let cond =
      match where with
      | None -> e_pattern
      | Some e_where -> binop `BAND e_pattern e_where
    in
    S_Cond (cond, stmt, tail) |> add_pos_from case
    (* End *)
  in
  (* Begin CasesToCond *)
  let cases_to_cond e0 cases =
    List.fold_right (case_to_cond e0) cases otherwise
    (* End *)
  in
  (* Begin DesugarCaseStmt *)
  match e0.desc with
  | E_Var _ -> (cases_to_cond e0 cases).desc
  | _ ->
      let x = fresh_var "__case__linearisation" in
      let decl_x = S_Decl (LDK_Let, LDI_Var x, None, Some e0) in
      S_Seq (decl_x |> add_pos_from e0, cases_to_cond (var_ x) cases)
(* End *)

type accessor_pair = { getter : stmt; setter : stmt; setter_arg : identifier }

let desugar_accessor_pair override name parameters args ty accessor_pair =
  let getter_func =
    {
      name;
      parameters;
      args;
      return_type = Some ty;
      body = SB_ASL accessor_pair.getter;
      subprogram_type = ST_Getter;
      recurse_limit = None;
      override;
      builtin = false;
    }
  in
  let setter_func =
    {
      name;
      parameters;
      args = (accessor_pair.setter_arg, ty) :: args;
      return_type = None;
      body = SB_ASL accessor_pair.setter;
      subprogram_type = ST_Setter;
      recurse_limit = None;
      override;
      builtin = false;
    }
  in
  [
    D_Func getter_func |> add_pos_from accessor_pair.getter;
    D_Func setter_func |> add_pos_from accessor_pair.setter;
  ]
