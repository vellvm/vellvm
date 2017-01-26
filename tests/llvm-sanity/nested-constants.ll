define i32 @foo () {
       %a = add i32 add (i32 1 , i32 2) , 2
       %b = add i32 add (i32 1 , i32 mul (i32 5, i32 7)) , 2
       %c = add i1 icmp eq (i32 1 , i32 mul (i32 5, i32 7)) , 1
       ret i32 %b 	  
}
