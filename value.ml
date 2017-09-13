(*========================================================================*)
(*                                                                        *)
(*             cppmem model exploration tool                              *)
(*                                                                        *)
(*                    Mark Batty                                          *)
(*                    Scott Owens                                         *)
(*                    Jean Pichon                                         *)
(*                    Susmit Sarkar                                       *)
(*                    Peter Sewell                                        *)
(*                                                                        *)
(*  This file is copyright 2011, 2012 by the above authors.               *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHE   *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(*========================================================================*)

(* TODO: error messages *)
(**
 * Values for the operational semantics, including constants and existential variables
 *)

let nextsym = ref 0

let gensym () = nextsym := !nextsym + 1; !nextsym

let pp_cst () = function
  | Cmm.Concrete n -> Printf.sprintf "%i" n
  | Cmm.Symbolic x -> x


(* TODO: parametrise this on an lval/rval argument, and include & in rval Const_id*)
let pp_value () = function
  | Cmm.Rigid r -> pp_cst () r
  | Cmm.Flexible x -> x

let subst_val s = function
  | Cmm.Rigid r -> Cmm.Rigid r
  | Cmm.Flexible x ->
    (try List.assoc x s
     with Not_found -> Cmm.Flexible x)

let subst_loc s l = subst_val s l



(* Inefficient!!! Store hashes or something else? *)
let seen_vars : string list ref = ref []

let reset_symbol_generation () =
  nextsym := 0;
  seen_vars := [];
  ()

let fresh_var_named n = 
  let varname = 
    if List.mem n !seen_vars then (n ^ string_of_int (gensym ())) else n
  in 
  seen_vars := varname :: !seen_vars;
  Cmm.Symbolic varname

let fresh_var () = Cmm.Flexible ("?v" ^ string_of_int (gensym ()))
(* let fresh_boolvar () = Boolvar (string_of_int (gensym ())) *)


let valuecompare v1 v2 = 
  match v1,v2 with
  | Cmm.Flexible vs1,Cmm.Flexible vs2 -> Pervasives.compare vs1 vs2
  | Cmm.Rigid (Cmm.Concrete i1),Cmm.Rigid (Cmm.Concrete i2) -> Pervasives.compare i1 i2
  | Cmm.Rigid (Cmm.Symbolic s1),Cmm.Rigid (Cmm.Symbolic s2) -> Pervasives.compare s1 s2
  | Cmm.Rigid (Cmm.Concrete _),Cmm.Rigid (Cmm.Symbolic _) -> -1
  | Cmm.Rigid (Cmm.Symbolic _),Cmm.Rigid (Cmm.Concrete _) -> 1
  | Cmm.Flexible _,Cmm.Rigid (Cmm.Concrete _) -> -1
  | Cmm.Rigid (Cmm.Concrete _),Cmm.Flexible _ -> 1
  | Cmm.Flexible _,Cmm.Rigid (Cmm.Symbolic _) -> -1
  | Cmm.Rigid (Cmm.Symbolic _),Cmm.Flexible _ -> 1

type vloc = Cmm.cvalue (* Values in locations *)

let pp_vloc = pp_value
let fresh_loc = fresh_var

type substitution = 
    (Cmm.flexsym * Cmm.cvalue) list

let pp_substitution () s = 
  String.concat ", " 
    (List.map 
       (fun (vsym,v) -> 
	 Printf.sprintf "%a|->%a" pp_value (Cmm.Flexible vsym)  pp_value v)
       s)




