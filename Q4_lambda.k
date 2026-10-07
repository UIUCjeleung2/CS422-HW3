// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

requires "substitution.md"

module Q4_LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]

  syntax Val ::= Int | Bool
  syntax Exp ::= "-" Int
               > Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]

  syntax Exp ::= "let" KVar "=" Exp "in" Exp [macro]
  rule let X = E in E':Exp => (lambda X . E') E

  syntax Exp ::= "letrec" KVar KVar "=" Exp "in" Exp  [macro]
               | "mu" KVar "." Exp                    [binder]
  rule letrec F:KVar X = E in E' => let F = mu F . lambda X . E in E'

  syntax Exp ::= "callcc" Exp  [strict]
  //syntax Exp ::= "callCC" Exp  [strict]

  //syntax Exp ::= "callcc" Exp [macro]
  syntax Exp ::= "callCC" Exp  [macro]
  syntax Val ::= cc(K)

  syntax KVar ::= "g" [token] | "x" [token]
  syntax Exp ::= "escape" Exp [strict]
endmodule

module Q4_LAMBDA
  imports Q4_LAMBDA-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult ::= Val

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]

  rule - I => 0 -Int I
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E

  rule mu X . E => E[(mu X . E) / X]

  // callCC doesn't return to the rest of the continuation unless return was called
  // callcc does return no matter what

  // callCC using cc
  //rule <k> callCC V:Val ~> K:K => V cc(K) </k>

  // callcc using cc
  rule <k> (callcc V:Val => V cc(K)) ~> K </k>
  rule <k> cc(K) V ~> _ =>  V ~> K </k>

  // callcc using callCC
  //rule callcc V => callCC(lambda g . (g (V g)))

  // callCC using callcc
  rule <k> escape V:Val ~> _ => V </k>
  rule callCC V => callcc (lambda g . escape (V g))

endmodule