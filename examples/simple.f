/* Output: 3 */ 
succ succ succ 0;


/* skip over the first two `succ` */
/* Output: 1 */
succ succ (shift k in succ 0); 


/* skip over the second `succ` */
/* Output: 2 */
succ (reset succ (shift k in succ 0)); 


/* resume the captured continuation */
/* Output: 3 */
succ (shift k in k (k (k 0)));


/* type modification: from Nat to Bool */
/* Output 1 */
if (reset succ (shift k in true)) then 1 else 2;


