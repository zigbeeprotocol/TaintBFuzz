let run () =
  Self.result "Hello, world!";
  let product = 
    Self.feedback ~level:2 "Computing the product of 11 and 5..."; 
    11 * 5
  in
  Self.result "11 * 5 = %d" product
