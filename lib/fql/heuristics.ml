module Interp = Modules.Target.TargetInterp
module Target = Modules.Target.Ast_Target

module StringSet = Set.Make(String)
module IntSet = Set.Make(Int)

(* Generates the set of integers [0, n) *)
let rec int_range (n : int) : IntSet.t =
  if n <= 0
  then IntSet.empty
  else IntSet.add (n - 1) (int_range (n - 1))

let string_set = StringSet.of_list

(* Find the os_distribution string in the given state or returns None *)
let get_dist (s : Interp.state) : string option =
  let State (elems, _) = s
  in let env =
    (("env", Target.Primitive Unit), Target.Literal (Unit (), Unit))
  in match Interp.ElementMap.find_opt env elems with
  | Some (Positive (State (_, attrs))) ->
      let os_distribution =
        ("os_distribution", Target.Primitive String)
      in begin match Interp.AttributeMap.find_opt os_distribution attrs with
      | Some (Literal (String d, _)) -> Some d
      | _ -> None
      end
  | _ -> None

(* Check that the users that are assumed to be present in r actually are
 * present given the set of users that exist, only checks the branches where
 * the os_distribution (in the query) matches if one is specified, this allows for
 * different configurations between different OSes. *)
let valid_users (users : StringSet.t) (dist : string option)
  (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { base; diff = { branches; inits; _ } } ->
        let dist_matches =
          match dist with
          | None -> true
          | Some dist ->
            match get_dist base with
            | Some d -> d = dist
            | None -> false
        in if dist_matches
        then 
          let all_set = int_range branches
          in let MergedDiff (elems, _) = inits
          in Interp.ElementMap.for_all (fun ((elem, _), arg) binding ->
            let (all_pos, all_neg) =
              let { Verifier.pos; neg; _ } = binding
              in let pos_set = IntSet.of_list pos
              in let neg_set = IntSet.of_list neg
              in (IntSet.equal pos_set all_set, IntSet.equal neg_set all_set)
            in match elem with
            | "e_user" ->
                begin match arg with
                | Literal (String nm, _) ->
                  if all_pos && not (StringSet.mem nm users)
                  then false
                  else if all_neg && StringSet.mem nm users
                  then false
                  else true
                (* If we don't know the value of the user, the conservative
                 * approach is to accept it. Could explore other options but
                 * this cause issues when dealing with files with unknown
                 * owners *)
                | _ -> true
                end
            | _ -> true
          ) elems
        else true
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r

let valid_groups (groups : StringSet.t) (dist : string option)
  (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { base; diff = { branches; inits; _ } } ->
        let dist_matches =
          match dist with
          | None -> true
          | Some dist ->
              match get_dist base with
              | Some d -> d = dist
              | None -> false
        in if dist_matches
        then 
          let all_set = int_range branches
          in let MergedDiff (elems, _) = inits
          in Interp.ElementMap.for_all (fun ((elem, _), arg) binding ->
            let (all_pos, all_neg) =
              let { Verifier.pos; neg; _ } = binding
              in let pos_set = IntSet.of_list pos
              in let neg_set = IntSet.of_list neg
              in (IntSet.equal pos_set all_set, IntSet.equal neg_set all_set)
            in match elem with
            | "e_group" ->
                begin match arg with
                | Literal (String nm, _) ->
                  if all_pos && not (StringSet.mem nm groups)
                  then false
                  else if all_neg && StringSet.mem nm groups
                  then false
                  else true
                | _ -> true
                end
            | _ -> true
          ) elems
        else true
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r

(* Checks that extra installed (i.e., final state) packages in the diff are
 * valid. Here pkgmgr is None or a pair of the OS distribution and package
 * manager *)
let valid_packages (packages : StringSet.t) (pkgmgr : (string * string) option)
  (r : Verifier.merged_res) : bool =
  let rec validate_res (r : Verifier.merged_res) : bool =
    match r with
    | Satisfied { base; diff = { branches; finals; _ } } ->
        let dist_matches =
          match pkgmgr with
          | None -> true
          | Some (dist, _) ->
              match get_dist base with
              | Some d -> d = dist
              | None -> false
        in if not dist_matches
        then true
        else
          let all_set = int_range branches
          in let rec validate_diff (d : Verifier.merged_diff) : bool =
            let MergedDiff (elems, _) = d
            in Interp.ElementMap.for_all (fun ((elem, _), arg) binding ->
              (* To install or uninstall the package it has to exist, so just
               * need all branches to do something with the package *)
              let all_install =
                let { Verifier.pos; neg; _ } = binding
                in IntSet.equal all_set 
                    (IntSet.union (IntSet.of_list pos) (IntSet.of_list neg))
              in if not all_install || elem <> "e_package"
              then validate_diff binding.diff
              else
                begin match arg with
                | Literal (String nm, _) ->
                    let manager_matches =
                      match pkgmgr with
                      | None -> true
                      | Some (_, mgr) ->
                          let MergedDiff (nested, _) = binding.diff
                          in Interp.ElementMap.mem 
                              ((mgr, Primitive Unit), Literal (Unit (), Unit))
                              nested
                    in if manager_matches
                    then
                      if StringSet.mem nm packages
                      then true
                      else false
                    else true
                (* I don't know why we would be installing a mysterious
                 * package, so rejecting for now *)
                | _ -> false
                end
            ) elems
          in validate_diff finals
    | Both (x, y) -> validate_res x && validate_res y
    | Either (x, y) -> validate_res x || validate_res y
  in validate_res r
