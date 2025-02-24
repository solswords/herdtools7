(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2012-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(***************************************************)
(* Translate LISA fake dependencies into real ones *)
(***************************************************)

open Printf

module type Config = sig
  val verbose : int
  val sync : bool
  val deref : bool
  val check_name : string -> bool
end

module Make(Config:Config)(Out:OutTests.S) =
  struct
    module D = Splitter.Default
    module LU = LexUtils.Make(D)
    module S = Splitter.Make(D)
    module OutStr = struct
      type t = Buffer.t
      let put_char b c = Buffer.add_char b c
      let put b s = Buffer.add_string b s
    end

    module W = Warn.Make(Config)

    module TR =
      TrTrue.Make
        (Config)
        (OutStr)

    let from_chan idx_out fname in_chan =
      try
        let { Splitter.locs = locs; start = start; name; arch; _} =
          S.split fname in_chan in
        if Config.check_name name.Name.name then begin
          match arch with
          | `LISA ->
              let buff = Buffer.create 256 in
              let
                  (_init_start,_init_end),
                (code_start,_code_end as code_sec),
                (constr_start,_constr_end),
                (_last_start,loc_eof) = locs in
              let echo sec =
                let lexbuf = LU.from_section sec in_chan in
                Echo.echo_fun lexbuf (Buffer.add_char buff)  in
              echo (start,code_start) ;
              let ok = TR.tr buff (LU.from_section code_sec in_chan) in
              if ok then begin
                echo (constr_start,loc_eof) ;
                let base = Filename.basename fname in
                let out = Out.open_file base in
                Misc.output_protect_close Out.close
                  (fun out ->
                    Out.fprintf out "%s" (Buffer.contents buff))
                  out ;
                Out.fprintf idx_out "%s\n" base
              end
          | `C ->
              let buff = Buffer.create 256 in
              let  _,_,_,(_,loc_eof) = locs in
              let echo sec =
                let lexbuf = LU.from_section sec in_chan in
                Echo.echo_fun lexbuf (Buffer.add_char buff)  in
              echo (start,loc_eof) ;
              let base = Filename.basename fname in
              let out = Out.open_file base in
              Misc.output_protect_close Out.close
                (fun out ->
                  Out.fprintf out "%s" (Buffer.contents buff))
                out ;
              Out.fprintf idx_out "%s\n" base
          | _ -> ()
        end else begin
            W.warn "%s: rejected by name" (Pos.str_pos0 fname)
        end
      with LexMisc.Error (msg,pos) ->
        Printf.eprintf
          "%a: Lex error %s (in %s)\n" Pos.pp_pos pos msg fname ;
        raise Misc.Exit

          let from_file idx_chan name =
            try
              Misc.input_protect
                (fun in_chan -> from_chan idx_chan name in_chan)
                name
            with Misc.Exit -> ()
            | Misc.Fatal msg|Misc.UserError msg ->
                eprintf "Fatal error is not fatal, %s\n" msg

          let from_args args =
            let idx_out = Out.open_all () in
            Misc.output_protect_close Out.close
              (fun idx_out ->
                Misc.iter_argv_or_stdin (from_file idx_out) args)
              idx_out ;
            Out.tar ()

        end

(**********)
(* Driver *)
(**********)

let tar = ref None
and verbose = ref 0
and aarch64 = ref false
let names = ref []
let oknames = ref StringSet.empty
let excl = ref []
let nonames = ref StringSet.empty
let set_tar x = tar := Some x
let args = ref []

let opts =
  [ "-v",
    Arg.Unit (fun () -> incr verbose),
    " be verbose";
    "-o", Arg.String set_tar,
    "<name> output to directory or tar file <name>" ;
    "-aarch64",
    Arg.Bool (fun b -> aarch64 := b),
    sprintf "<bool> reduce tests for aarch64 (no deref, no sync) default %b" !aarch64;
    CheckName.parse_names names ;
    CheckName.parse_oknames oknames ;
    CheckName.parse_excl excl ;
    CheckName.parse_nonames nonames ;
  ]

let prog =
  if Array.length Sys.argv > 0 then Sys.argv.(0)
  else "recond"

let () =
  Arg.parse opts
    (fun a -> args := a :: !args)
    (sprintf "Usage %s [options] [test]*" prog)

(* Read names *)
let from_args =
  let module Check =
    CheckName.Make
      (struct
        let verbose = !verbose
        let rename = []
        let select = []
        let names = !names
        let oknames = !oknames
        let excl = !excl
        let nonames = !nonames
      end) in
  let module X =
    Make
      (struct
        let verbose = !verbose
        let sync = false
        let deref = !aarch64
        let check_name = Check.ok
      end) in
  match !tar with
  | None ->
      let module Y = X(OutStd) in
      Y.from_args
  | Some _ as t ->
      let module T =
        OutTar.Make
          (struct
            let verbose = !verbose
            let outname = t
          end) in
      let module Y = X(T) in
      Y.from_args

let () = from_args !args
