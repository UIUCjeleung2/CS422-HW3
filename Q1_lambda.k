

module Q1_LAMBDA-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Val ::= Id | "lambda" Id "." Exp
    syntax Exp ::= Val
                  | Exp Exp     [strict, left]          // Make sure to evaluate the subexpressions before trying semantic rules
                  | "(" Exp ")" [bracket]
    syntax Val ::= Int | Bool
    syntax Exp ::= "-" Int
                > Exp "*" Exp   [strict, left]
                | Exp "/" Exp   [strict]
                > Exp "+" Exp   [strict, left]
                > Exp "<=" Exp  [strict]
                > Exp "==" Exp  [strict]
                > left: "if" Exp "then" Exp "else" Exp   [strict(1)]
                > left: "let" Id "=" Exp "in" Exp        [macro]
                    > left: "letrec" Id Id "=" Exp "in" Exp [macro]
                    > left: "mu" Id "." Exp              [macro]
        

        rule let X = E in E':Exp => (lambda X . E') E

        // No need for a combinator with whatever this mu thing is
        rule letrec F:Id X:Id = E in E' => let F = mu F . lambda X . E in E'
    
    syntax Id ::= "f" [token] | "x" [token] | "v" [token]
endmodule

module Q1_LAMBDA
    imports Q1_LAMBDA-SYNTAX
    imports DOMAINS

    // freeVars(Exp) returns a set of something
    syntax Set ::= freeVars(Exp)            [function]
    rule freeVars( _ )                   => .Set [owise]
    rule freeVars( V:Id )                => SetItem(V)                          // A variable by itself is free
    rule freeVars( lambda X . E )        => freeVars(E) -Set SetItem(X)         // The vars in E are free, except for the arg of the lambda function X
    rule freeVars( E1 E2 )               => freeVars(E1) freeVars(E2)           // Get the freevars of two sequential expressions
    rule freeVars( E1 * E2 )             => freeVars(E1) freeVars(E2)
    rule freeVars( E1 / E2 )             => freeVars(E1) freeVars(E2)
    rule freeVars( E1 + E2 )             => freeVars(E1) freeVars(E2)
    rule freeVars( E1 <= E2 )            => freeVars(E1) freeVars(E2)
    rule freeVars( if B then E1 else E2) => freeVars(B) freeVars(E1) freeVars(E2)


    // Freshvar returns a new ID that has not been used, concatenating the ID with an Int until we find something that works
    syntax Id ::= freshVar(Id, Int, Set)    [function]
    rule freshVar(V, I, S)               => #let X = String2Id(Id2String(V) +String Int2String(I)) 
                                            #in #if X in S #then freshVar(V, I +Int 1, S) #else X #fi

    // This returns an Exp, but what is it used for?
    syntax Exp ::= Exp "[" Exp "/" Id "]"   [function]
    
    // Defines substitution of variables
    rule X:Exp [_ / _] => X [owise]         // Otherwise, return X
    rule X [V / X]     => V                 // If X[Exp / ID], return Exp. Such as X[42/X], we're trying to substitute X for 42

    // What are these
    // 1. [Anything / Y:ID] => Return the original lambda to prevent messing it up with a substitution.
    //     For example, we don't want to evaluate lambda y.(y + 1)[99 / y] => lambda y.(99 + 1) because
    //     we used a substitution with the same var name. So we output the same lambda and skip.
    //
    // 2. [V: Expression / X: ID], Y notin V => Return the lambda with the proper substitutions in the lambda function body.
    //    Examples:
    //        lambda y.(x + y)[99 / x] => lambda.y(99 + y)
    //        lambda y.(x + y)[(a + b) / x] => lambda.y((a + b) + y)
    //        lambda y.(x + y)[y / x] => DOES NOT WORK since y in freevars(V)
    //    The rest of the line requires that Y != X, and that Y isn't a variable in V.
    //
    // 3. [V: Expression / X: ID], Y in V => Return the lambda with the proper substitutions, given
    //    that Y is in the expression. It achieves this by doing two substitution passes:
    //        Substitute E[Z / Y] to get rid of the arg that may cause conflict
    //        Substitute E[V / X] which is the original pass.
    //    Example:
    //                                   # FIRST PASS           # SECOND PASS
    //        lambda y.(x + y)[y / x] => lambda z . (x + z) => lambda z . (y + z)
    //    As you can see, this rewrites the whole lambda expression to avoid the conflict that
    //    would have otherwise happened without this rule:
    //        lambda y.(x + y)[y / x] => lambda y.(y + y)       # THIS IS WRONG

    rule (lambda Y . E) [_ / Y] => lambda Y . E
    rule (lambda Y . E) [V / X] => lambda Y . (E[V / X]) requires Y =/=K X andBool notBool (Y in freeVars(V))
    rule (lambda Y . E) [V / X] => #let Z = freshVar(Y, 0, freeVars(E) freeVars(V)) #in lambda Z . (E[Z / Y] [V / X])
                                    requires Y =/=K X andBool Y in freeVars(V)

    // Do the same substitution on two sequential expressions
    rule (E1:Exp E2:Exp)    [V / X] => E1[V/X] (E2[V/X])
    rule (E1:Exp * E2:Exp)  [V / X] => E1[V/X] *  (E2[V/X])
    rule (E1:Exp / E2:Exp)  [V / X] => E1[V/X] /  (E2[V/X])
    rule (E1:Exp + E2:Exp)  [V / X] => E1[V/X] +  (E2[V/X])
    rule (E1:Exp <= E2:Exp) [V / X] => E1[V/X] <= (E2[V/X])
    rule (E1:Exp == E2:Exp) [V / X] => E1[V/X] == (E2[V/X])

    rule (if C then E1 else E2) [V / X] => if C[V/X] then E1[V/X] else (E2[V/X])

    syntax KResult ::= Val

    // Application of a lambda func to a Value
    // This is the rule that lambda programs start with, and then
    // we do substitutions along the way
    rule (lambda X:Id . E:Exp) V:Val => E[V / X]

    // Arithmetic operator definitions
    rule - I => 0 -Int I
    rule I1 * I2 => I1 *Int I2
    rule I1 / I2 => I1 /Int I2
    rule I1 + I2 => I1 +Int I2
    rule I1 <= I2 => I1 <=Int I2
    rule I1 == I2 => I1 ==Int I2
    
    // IF THEN ELSE
    rule if true then E else _ => E
    rule if false then _ else E => E

    // This replaces a every call of the function X inside of E
    // with a definition of itself, allowing for recursion

    rule mu X . E => (lambda f . ((lambda x . (f (lambda v . ((x x) v)))) (lambda x . (f (lambda v . ((x x) v)))))) (lambda X . E)


endmodule