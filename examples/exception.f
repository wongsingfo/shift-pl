let try = lambda try_with error_callback. 
    reset ( try_with (lambda error. shift ignored in (error_callback error)) )
in


try (lambda throws.
       if true then
            throws 213
       else 
            233)
    (lambda catch_error.
        666);


