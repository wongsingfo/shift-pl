let visit = fix visit. lst.
    lmatch lst {
        case nil => shift k in []
        case a :: rest => 
            a :: (shift k in
                        (k []) :: (reset k (visit rest))
            )
    } 
in let prefix = lambda lst. reset visit lst
in prefix [1, 2, 3, 4];

/* output: [[1], [1, 2], [1, 2, 3], [1, 2, 3, 4]] */
