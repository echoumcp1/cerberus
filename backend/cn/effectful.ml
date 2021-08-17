module type S = sig  type 'a t
  type 'a m
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end



module Make(T : S) = struct

  open T

  let (let@) = T.bind


  module ListM = struct

    open List

    let rec mapM (f : 'a -> 'b m) (l : 'a list) : ('b list) m = 
      match l with
      | [] -> return []
      | x :: xs -> 
         let@ y = f x in
         let@ ys = mapM f xs in
         return (y :: ys)


    let mapiM (f : int -> 'a -> 'b m) 
              (l : 'a list) : ('b list) m = 
      let rec aux i l =
        match l with
        | [] -> return []
        | x :: xs -> 
           let@ y = f i x in
           let@ ys = aux (i + 1) xs in
           return (y :: ys)
      in
      aux 0 l

    let iterM (f : ('a -> unit m)) (l : 'a list) : unit m = 
      let@ _ = mapM f l in 
      return ()

    let concat_mapM f l = 
      let@ xs = mapM f l in
      return (concat xs)

    let filter_mapM f l = 
      let@ xs = mapM f l in
      return (filter_map (fun x -> x) xs)



    let fold_leftM (f : 'a -> 'b -> 'c m) (a : 'a) (bs : 'b list) =
      Stdlib.List.fold_left (fun aM b -> let@ a = aM in f a b) (return a) bs

    (* maybe from Exception.lem *)
    let fold_rightM (f : 'b -> 'a -> 'c m) (bs : 'b list) (a : 'a) =
      Stdlib.List.fold_right (fun b aM -> let@ a = aM in f b a) bs (return a)

  end

  module List1M = struct

    open List1

    let mapM (f : 'a -> 'b m) (l : 'a list1) : ('b list1) m = 
      let (hd, tl) = dest l in
      let@ hd = f hd in
      let@ tl = ListM.mapM f tl in
      return (List1.make (hd, tl))

    let iterM (f : ('a -> unit m)) (l : 'a list1) : unit m = 
      let@ _ = mapM f l in 
      return ()  

  end


  module PmapM = struct

    let foldM 
          (f : 'k -> 'x -> 'y -> 'y m)
          (map : ('k,'x) Pmap.map) (init: 'y) : 'y m =
      Pmap.fold (fun k v aM -> let@ a = aM in f k v a) map (return init)

    let iterM f m = 
      Pmap.fold (fun k v m -> let@ () = m in f k v) 
        m (return ())

    let mapM 
          (f: 'k -> 'v -> 'w m)
          (m : ('k,'v) Pmap.map)
          (cmp: 'k -> 'k -> int)
        : (('k,'w) Pmap.map) m
      = 
      foldM (fun k v m -> 
          let@ v' = f k v in 
          return (Pmap.add k v' m)
        ) m (Pmap.empty cmp)

  end


end