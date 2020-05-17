let (+) = fix add. a b. 
  if iszero a 
  then b
  else add (pred a) (succ b)
in let (*) = fix mul. a b.
  if iszero a 
  then 0 
  else b + (mul (pred a) b)
in let choose = lambda a b. 
  shift k in (k a) + (k b)
in reset 
    let a = choose 1 2 in 
    let b = choose 3 4 in 
    a * b;

let (+) = fix add. a b. 
  if iszero a 
  then b
  else add (pred a) (succ b)
in let append = fix append. l1 l2.
  lmatch l1 {
    case nil => l2 
    case hd :: tl => hd :: append tl l2
  }
in let choose = lambda a b. 
  shift k in append (k a) (k b)
in reset 
    let a = choose 1 2 in 
    let b = choose 3 4 in 
    [a + b];
