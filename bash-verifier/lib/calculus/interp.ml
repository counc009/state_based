open Ast
open Value
open State

module type INTERP_UTILS = sig
  module C : AST
  module V : VALUE with type lit = C.lit

  val as_bool : V.t -> bool option
  val as_list : V.t -> V.t list option
  val of_list : V.t list -> V.t

  val func_def : C.func -> V.t -> V.t option
  val act_def : C.act -> C.stmt
end

let ( let* ) = Option.bind

module Interp (I : INTERP_UTILS)(ST : STATE) = struct
  module C = I.C
  module V = I.V
  module S = ST(V)

  module VarMap = Map.Make(String)
  type env = V.t VarMap.t

  let init_env : env = VarMap.singleton "σ" (V.SRef V.Here)

  let interp_expr (e : C.expr) (env : env) : V.t option =
    let rec interp = function
      | C.Literal l -> Some (V.Literal l)
      | C.Pair (x, y) ->
          let* x = interp x
          in let* y = interp y
          in Some (V.Pair (x, y))
      | C.Variable v -> VarMap.find_opt v env
      | C.Function (f, e) ->
          let* e = interp e
          in I.func_def f e
      | C.Element (b, elem, e) ->
          let* b = interp b
          in let* e = interp e
          in match b with
          | V.SRef b ->
              Some (V.SRef (V.Nested (elem, e, b)))
          | _ -> None
    in interp e

  type interp_res = Continue of env * S.t
                  | Raise    of V.t * env * S.t
                  | Return   of V.t * env * S.t
                  | Yield    of V.t * env * S.t
                  | Failure

  let get_attr = S.get_attr ~failure:Failure
  let check_elem = S.check_elem
  let localize =
    let update x update =
      match x with
      | Continue (env, st)  -> Continue (env, update st)
      | Raise (v, env, st)  -> Raise (v, env, update st)
      | Return (v, env, st) -> Return (v, env, update st)
      | Yield (v, env, st)  -> Yield (v, env, update st)
      | Failure             -> Failure
    in S.localize ~failure:Failure ~update

  let ( let^ ) (r : interp_res) (f : (env * S.t) -> interp_res) : interp_res =
    match r with
    | Continue (e, s) -> f (e, s)
    | _ -> r

  let ( let& ) (v : 'a option) (f : 'a -> interp_res) : interp_res =
    match v with
    | None -> Failure
    | Some v -> f v

  let ( let$ ) (v : V.t option) (f : V.s -> interp_res) : interp_res =
    match v with
    | Some (V.SRef s) -> f s
    | _ -> Failure

  let ( let> ) (v : ('a -> 'b) -> 'c) (f : 'a -> 'b) : 'c = v f

  let rec interp (s : C.stmt) (env : env) (st : S.t) : interp_res =
    match s with
    | C.Pass -> Continue (env, st)
    | C.Seq (x, y) ->
        let^ (env, st) = interp x env st
        in interp y env st

    | C.Raise e ->
        let& e = interp_expr e env
        in Raise (e, env, st)
    | C.Return e ->
        let& e = interp_expr e env
        in Return (e, env, st)
    | C.Yield e ->
        let& e = interp_expr e env
        in Yield (e, env, st)

    | C.Assign (v, e) ->
        let& e = interp_expr e env
        in Continue (VarMap.add v e env, st)

    | C.Action (v, act, e) ->
        let& e = interp_expr e env
        in begin match interp (I.act_def act) init_env st with
        | Return (res, _, st) -> Continue (VarMap.add v res env, st)
        | Raise (v, _, st) -> Raise (v, env, st)
        | Continue (_, _) -> Failure (* a continue across functions, invalid *)
        | Yield (_, _, _) -> Failure (* a yield across functions, invalid *)
        | Failure -> Failure
        end

    | C.Add (C.QualAttr (base, attr, e)) ->
        let$ base = interp_expr base env
        in let& e = interp_expr e env
        in let& st = S.set_attr st base attr e
        in Continue (env, st)
    | C.Add (C.QualPosE (base, elem, e)) ->
        let$ base = interp_expr base env
        in let& e = interp_expr e env
        in let& st = S.pos_elem st base elem e
        in Continue (env, st)
    | C.Add (C.QualNegE (base, elem, e)) ->
        let$ base = interp_expr base env
        in let& e = interp_expr e env
        in let& st = S.neg_elem st base elem e
        in Continue (env, st)

    | C.Get (v, (base, attr)) ->
        let$ base = interp_expr base env
        in let> (st, res) = get_attr st base attr
        in Continue (VarMap.add v res env, st)

    | C.Contains ((base, elem, e), thn, els) ->
        let$ base = interp_expr base env
        in let& e = interp_expr e env
        in let> (st, present) = check_elem st base elem e
        in if present
        then interp thn env st
        else interp els env st

    | C.Cond (e, thn, els) ->
        let& e = interp_expr e env
        in begin match I.as_bool e with
        | Some true -> interp thn env st
        | Some false -> interp els env st
        | None -> Failure
        end

    | C.Match (e, v, lft, rht) ->
        let& e = interp_expr e env
        in begin match e with
        | V.Left e -> interp lft (VarMap.add v e env) st
        | V.Right e -> interp rht (VarMap.add v e env) st
        | _ -> Failure
        end

    | C.ForEach (v_res, e, v, body) ->
        let& e = interp_expr e env
        in begin match I.as_list e with
        | Some xs ->
            let (res, status) =
              List.fold_left (fun (res, status) x ->
                match status with
                | Continue (env, st) ->
                    begin match interp body (VarMap.add v x env) st with
                    | Continue (env, st) -> (res, Continue (env, st))
                    | Yield (v, env, st) -> (v :: res, Continue (env, st))
                    | status -> (res, status)
                    end
                | _ -> (res, status)
              ) ([], Continue (env, st)) xs
            in let^ (env, st) = status
            in Continue (VarMap.add v_res (I.of_list (List.rev res)) env, st)
        | None -> Failure
        end

    | C.While (e, body) ->
        let& cond = interp_expr e env
        in begin match I.as_bool cond with
        | None -> Failure
        | Some false -> Continue (env, st)
        | Some true -> interp (C.Seq (body, C.While (e, body))) env st
        end

    | C.TryCatch (body, v_ex, catch) ->
        begin match interp body env st with
        | Raise (v, env, st) -> interp catch (VarMap.add v_ex v env) st
        | res -> res
        end

    | C.TryFinally (body, finally) ->
        (* A finally block always executes, regardless of how the body returned
         * (unless it failed to interpret, in which case we just fail as well.
         * If the finally block hits a terminator (a yield, return, or raise)
         * we use that for our result, unless it performs a yield and the body
         * had performed a return or raise, in which case we use that as our
         * result still. *)
        begin match interp body env st with
        | Continue (env, st) -> interp finally env st
        | Raise (v, env, st) ->
            begin match interp finally env st with
            | Continue (env, st) | Yield (_, env, st) -> Raise (v, env, st)
            | res -> res
            end
        | Return (v, env, st) ->
            begin match interp finally env st with
            | Continue (env, st) | Yield (_, env, st) -> Return (v, env, st)
            | res -> res
            end
        | Yield (v, env, st) ->
            let^ (env, st) = interp finally env st
            in Yield (v, env, st)
        | Failure -> Failure
        end

    | C.Localize (elem, e, body) ->
        let& e = interp_expr e env
        in let> st = localize st elem e
        in interp body env st
end
