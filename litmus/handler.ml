(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2022-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(** Arch dependent code for exception handlers *)

module type S = sig
  type ins
  (* Strictly greater than any label in handler *)
  val max_handler_label : int

  (* Emit code to and from user mode *)
  val user_mode : bool -> Proc.t -> ins list
  val kernel_mode : bool -> ins list

  (* Explicit handlers prologue and epilogue *)
  val fault_handler_prologue : bool -> Proc.t -> ins list
  val fault_handler_epilogue : bool -> ins list -> ins list
end

module No(A:sig type ins end) =
struct
  type ins = A.ins

  let max_handler_label = 0
  let user_mode _ _ = [] and kernel_mode _ = []

  let fault_handler_prologue _ _ = assert false
  let fault_handler_epilogue _ _ = assert false
end
