module Target = Target.Ast_Target

module type FORMAT = sig
  type t
  (* Integer specifies the number of spaces to add each indentation level *)
  val from_channel : out_channel -> int -> t
  val indent : t -> unit
  val unindent : t -> unit
  val println : t -> ('a, unit, string, unit) format4 -> 'a
end

module Format : FORMAT = struct
  type t = { out : out_channel; step : int; mutable indent : string list }

  let from_channel chan n = { out = chan; step = n; indent = [] }
  
  let indent fmt =
    let cur =
      match fmt.indent with
      | [] -> ""
      | c :: _ -> c
    in fmt.indent <- (String.make fmt.step ' ' ^ cur) :: fmt.indent

  let unindent fmt =
    fmt.indent <-
      match fmt.indent with
      | [] -> []
      | _ :: tl -> tl

  let println (fmt : t) : ('a, unit, string, unit) format4 -> 'a =
    let do_print (s : string) =
      let out = fmt.out
      in let indent =
        match fmt.indent with
        | [] -> ""
        | h :: _ -> h
      in let lines = String.split_on_char '\n' s
      in List.iter (Printf.fprintf out "%s%s\n" indent) lines
    in Printf.ksprintf do_print
end

let lean_of_expr (_e : Target.expr) : string = failwith "TODO"

let lean_of_qual (_q : Target.qual) : string = failwith "TODO"

let lean_of_attr (_a : Target.attr) : string = failwith "TODO"

let lean_of_elem (_e : Target.elem) : string = failwith "TODO"

(* TODO: We need to collect all of the local variables (used in assignments)
 * and declare all of them as mutuable variables at the start of our generated
 * code (let mut <id> := Value.Literal Lit.UnitLit)
 * Also, need to collect all of the actions and their statements and code gen
 * them.
 * We also need to quote the identifiers with « » *)

let rec lean_of_stmt (fmt : Format.t) (s : Target.stmt) : unit =
  match s with
  | Seq (x, y) ->
      lean_of_stmt fmt x; lean_of_stmt fmt y
  | Pass ->
      Format.println fmt "pure ()"
  | Assign (v, e) ->
      Format.println fmt "let %s := (%s)" v (lean_of_expr e)
  | Add q ->
      Format.println fmt "add (%s)" (lean_of_qual q)
  | Get (v, a) ->
      Format.println fmt "let %s <- attrGet (%s)" v (lean_of_attr a)
  | Contains (el, th, es) ->
      Format.println fmt "if (<- contains (%s))\nthen" (lean_of_elem el);
      Format.indent fmt;
      lean_of_stmt fmt th;
      Format.unindent fmt;
      Format.println fmt "else";
      Format.indent fmt;
      lean_of_stmt fmt es;
      Format.unindent fmt
  | Cond (c, th, es) ->
      Format.println fmt "match (%s)\nwith" (lean_of_expr c);
      Format.println fmt "| Value.Literal (Lit.BoolLit True) =>";
      Format.indent fmt;
      lean_of_stmt fmt th;
      Format.unindent fmt;
      Format.println fmt "| Value.Literal (Lit.BoolLit False) =>";
      Format.indent fmt;
      lean_of_stmt fmt es;
      Format.unindent fmt;
      Format.println fmt "| _ => failure"
  | Match (e, v, lft, rht) ->
      Format.println fmt "match (%s) with" (lean_of_expr e);
      Format.println fmt "| Value.Left %s =>" v;
      Format.indent fmt;
      lean_of_stmt fmt lft;
      Format.unindent fmt;
      Format.println fmt "| Value.Right %s =>" v;
      Format.indent fmt;
      lean_of_stmt fmt rht;
      Format.unindent fmt;
      Format.println fmt "| _ => failure"
  | Raise e ->
      Format.println fmt "throw (%s)" (lean_of_expr e)
  | Return e ->
      Format.println fmt "return (%s)" (lean_of_expr e)
  (* TODO: Action, ForEach, Localize, Yield *)
  | _ -> failwith "TODO"
