let add = fix add. a b. 
  if iszero a 
  then b
  else add (pred a) (succ b)
in let mul = fix mul. a b.
  if iszero a 
  then 0 
  else add b (mul (pred a) b)
in let choose = lambda a b. 
  shift k in add (k a) (k b)
in reset 
    let a = choose 1 2 in 
    let b = choose 3 4 in 
    mul a b;

let add = fix add. a b. 
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
    [add a b];
