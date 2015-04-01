(*********************************************************************)
(*                         Diy                                       *)
(*                                                                   *)
(*        Luc Maranget INRIA Paris-Rocquencourt, France.             *)
(*                                                                   *)
(*  Copyright 2015 Institut National de Recherche en Informatique et *)
(*  en Automatique. All rights reserved. This file is distributed    *)
(*  under the terms of the Lesser GNU General Public License.        *)
(*********************************************************************)

open Printf
open Code

module type Config = sig
  val debug : Debug.t
  val verbose : int
  val libdir : string
  val prog : string
  val bell : string option
end

module Make(O:Config) = struct

include BellBase

let bi = match O.bell with
| Some fname ->
    let module R =
    ReadBell.Make
      (struct
        let debug_lexer = O.debug.Debug.lexer
        let debug_model = O.debug.Debug.model
        let verbose = O.verbose        
        let libfind =
          let module ML =
            MyLib.Make
              (struct
               let includes = []
               let libdir = O.libdir
              end) in
          ML.find
        let prog = O.prog
      end) in
  Some (R.read fname)
| None -> None

let scopegen = match bi with
| None ->
    let module M = ScopeGen.NoGen in
    (module M : ScopeGen.S)
| Some bi ->
    let module M =
      ScopeGen.Make
        (struct
          let debug = false
          let info = bi
        end) in
    (module M : ScopeGen.S)

module ScopeGen =  (val scopegen : ScopeGen.S)

(* Should check non-ambiguity *)
let pp_annot a = match a with
| "atomic" -> "A"
| "ordinary" -> "P"
| _ ->
    let len = String.length a in
    match len with
    | 0 -> assert false
    | _ ->
        let fst = a.[0] in
        sprintf "%c%s"
          (Char.uppercase fst)
          (String.sub a 1 (len-1))
(*
    let len = String.length a in
    match len with
    | 0 -> ""
    | 1|2|3 ->
        let fst = a.[0] in
        sprintf "%c%s"
          (Char.uppercase fst)
          (String.sub a 1 (len-1))
    | _ ->
        let fst = a.[0] in
        sprintf "%c%s"
          (Char.uppercase fst)
          (String.sub a 1 2)
*)      

(* No atoms yet *)

type atom = string list

let default_atom = [] (* Wrong, extract from bell file? *)

let tr_dir = function
  | R -> BellName.r
  | W -> BellName.w

let applies_atom = match bi with
| None -> (fun a _d -> match a with [] -> true | _ -> false)
| Some bi -> (fun a d -> BellModel.check_event (tr_dir d) a bi)

let applies_atom_rmw _ar _aw = true (* Wrong, extract from bell file? *)

let pp_plain = "P"
let pp_as_a = None

let pp_annots a =
  String.concat "" (List.map pp_annot a)

let pp_atom a =  pp_annots a

let compare_atom a1 a2 =
  Misc.list_compare String.compare a1 a2


let fold_annots eg f r =
  List.fold_left
    (fun r ag ->
      Misc.fold_cross (List.map StringSet.elements ag) f r)
    r eg
        

let fold_annots_dir bi d f r =
  let eg = BellModel.get_events (tr_dir d) bi in
  fold_annots eg f r
        

let fold_atom = match bi with
| None -> fun _f r -> r
| Some bi ->
    fun f r ->
      fold_annots_dir bi R f (fold_annots_dir bi W f r)

let worth_final _ = false

(* End of atoms *)

(**********)
(* Fences *)
(**********)

type fence = barrier

let is_isync _ = false

let compare_fence = barrier_compare

let strong = Fence []

let pp_fence (Fence a) = sprintf "Fence%s" (pp_annots a)

let fold_fences = match bi with
| None -> fun _f k -> k
| Some bi ->
    fun f k ->
      let eg = BellModel.get_events BellName.f bi in
      fold_annots eg (fun a k -> f (Fence a) k)  k

let fold_cumul_fences _f k = k
let fold_all_fences  = fold_fences
let fold_some_fences f k = f strong k

let orders _ _ _ = true

(********)
(* Deps *)
(********)

include StdDep

include
    ArchExtra.Make
    (struct
      type arch_reg = reg

      let is_symbolic _ = false

      let pp_reg = pp_reg
      let free_registers = allowed_for_symb
    end)
end
