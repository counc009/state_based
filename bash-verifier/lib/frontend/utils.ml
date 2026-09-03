let map_result (f : 'a -> ('b, 'e) result) (xs : 'a list) : ('b list, 'e) result =
  let rec map (xs : 'a list) =
    match xs with
    | [] -> Ok []
    | x :: xs ->
        Result.bind (f x) (fun y ->
          Result.bind (map xs) (fun ys ->
            Ok (y :: ys)))
  in map xs
