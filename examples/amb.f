let (+) = fix add. a b. 
  if iszero a 
  then b
  else add (pred a) (succ b)
in let (*) = fix mul. a b.
  if iszero a 
  then 0 
  else b + (mul (pred a) b)
in let equal = fix equal. a b. 
       if iszero a then iszero b
  else if iszero b then iszero a
  else equal pred a pred b
in let append = fix append. l1 l2.
  lmatch l1 {
    case nil => l2 
    case hd :: tl => hd :: append tl l2
  }
in let choose_from_list = lambda l. shift k in (fix choose. l k.
  lmatch l {
    case nil => []
    case hd :: tl => append (k hd) (choose tl k)
  } ) l k
in let fail = lambda ignored. []
in let success = lambda result. [result]
in reset 
    let a = choose_from_list [1, 2, 3, 4, 12] in 
    let b = choose_from_list [1, 2, 4, 5, 6, 7] in 
    let result = a * b in
    if equal result 12 then 
      success [a, b]
    else 
      fail false;
