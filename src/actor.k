/* Let us use prefix forms for everything because I am tired of parsing
 * ambiguities.
 */

require "substitution.k"

module ACTOR-SYNTAX

  imports SUBSTITUTION
  
  /* Atoms */
  
  syntax Atm  ::= Int
                | "t"
                | "nil"
  
  /* Values are terms that cannot rewrite anymore. */

  syntax Val  ::= Atm
                | Id                                    // variables
                | "lambda" "(" Id "," Exp ")" [binder]  // lambda abstraction
                | PairVal                               // pairs
  syntax PairVal ::= "pr" "(" Val "," Val ")"

  /* Expressions */
  
  syntax Exp  ::= Val                        // values
  
  syntax Exp  ::= "app" "(" Exp "," Exp ")" [seqstrict] // lambda application
  
  syntax Val  ::= "rec" "(" Exp ")" // call-by-value fixed-point combinator

  /* Expressions that are constructed using primitive operations. */
  
  syntax Exp  ::= "isatom"  "(" Exp                 ")"
                | "isnat"   "(" Exp                 ")"
                | "ispr"    "(" Exp                 ")" 
                | "br"      "(" Exp "," Exp "," Exp ")" [strict(1)]
                | "pr"      "(" Exp "," Exp         ")" 
                | "fst"     "(" Exp                 ")" 
                | "snd"     "(" Exp                 ")" 
                | "newadr"  "("                     ")" 
                | "initbeh" "(" Exp "," Exp         ")" 
                | "send"    "(" Exp "," Exp         ")" 
                | "become"  "(" Exp                 ")"

  /* Expressions that are syntactic sugar.
   * They don't need the [strict] attribute as they simply rewrite
   * to expressions with primitive operations
   */
  syntax Exp  ::= "if" "(" Exp "," Exp "," Exp ")" 
                | "let" "(" Binding "," Exp ")"
                | "seq" "(" Exp "," Exp ")"
                | "letactor" "(" Bindings "," Exp ")"

  /* Bindings and lists of bindings */
  
  syntax Binding  ::= "bind" "(" Id "," Exp ")"
  syntax Bindings ::= List{Binding, ","}

  /* Expressions that are constructed using more operations. */
  syntax Exp ::= "mkset" "(" Exp ")"
               | "mkget" "(" Exp ")"
               | "set?"  "(" Exp ")"
               | "get?"  "(" Exp ")"
               | "eq?"   "(" Exp "," Exp ")" [strict]
               | "left"  "(" Exp ")"
               | "right" "(" Exp ")"
               | "cust"  "(" Exp ")"
  
  /* User-defined actor behavior as expressions. */
  syntax Exp ::= "treeprod"
               | "joincont"
               
  /* Message */
  syntax Message ::= "msg" "(" Val "," Val ")"  // message < lhs <= rhs >
  
  /* Actor states */
  syntax AState  ::= "uninit" "(" Id  ")"            // (?a) uninitialized
                   | "ready"  "(" Val ")"            // (b)  ready to accept msg
                   | "exec"   "(" Exp ")"  [strict]  // [e]  busy executing e
                   
  /* Communication values */
  syntax CVal    ::= Atm
                   | Id
                   | "pr" "(" CVal "," CVal ")"

  /* Meta-level information for rewriting */
  syntax KVariable ::= Id
  syntax KResult   ::= Val
                     | CVal
  
endmodule

module ACTOR

  imports ACTOR-SYNTAX
  
  syntax Id ::= "a" // the id of actor in the initial configuration

  configuration <T color="red">
                  <actors color="orange">
                    <actor multiplicity="*" color="yellow">
                      <k color="green"> exec($PGM:Exp) </k>
		      <id> a </id>
                    </actor>
                  </actors>
                  <messages> .List </messages>
                  <definedaddr> ListItem(a) </definedaddr>
                  <ext> .List </ext>
		  <recep> .List </recep>
                </T>
  
  /* Desugar rules for syntactic sugar (page 15) */
  
  rule if(E0:Exp, E1:Exp, E2:Exp)
    => app(br(E0, lambda(!Z, E1), lambda(!Z, E2)), nil)
   
  rule let(bind(X:Id, E0:Exp), E1)
    => app(lambda(X, E1), E0)
    
  rule seq(E0:Exp, E1:Exp)
    => app(app(lambda(!Z, lambda(!X, !X)), E0), E1)
  
  rule letactor(.Bindings, E:Exp)
    => E:Exp
  rule letactor(bind(X1:Id, E1:Exp), E:Exp)
    => let(bind(X1, newadr()),
         seq(initbeh(X1, E1), E))
  rule letactor((bind(X1:Id, E1:Exp), bind(X2:Id, E2:Exp)), E:Exp) // FIXME
    => let(bind(X1, newadr()),
       let(bind(X2, newadr()),
         seq(initbeh(X1, E1),
         seq(initbeh(X2, E2), E))))
         
  /* Reduction rule for fixed-point combinator (I wrote it by myself) */
  
  rule rec(lambda(B:Id, E:Exp)) => E[rec(lambda(B, E)) / B] [structural]

  /* Reduction rules of expressions (page 18) */
  
  /* (beta-v) */
  rule app(lambda(X:Id, E:Exp), V:Val) => E[V / X]
  
  /* (delta) rules are defined for each operators */
  
  /* (br) */
  rule br(nil  , V1:Val, V2:Val) => V2
  rule br(V:Val, V1:Val, V2:Val) => V1       // FIXME consider known addresses
    requires V:Val =/=K nil
    
  /* (ispr) */
  rule ispr(V:PairVal) => t
  rule ispr(V:Val)     => nil                // FIXME consider known addresses
    requires notBool(isPairVal(V))
  
  /* (fst) & (snd) */
  rule fst(pr(V1:Val, V2:Val)) => V1:Val
  rule snd(pr(V1:Val, V2:Val)) => V2:Val
  
  /* (eq) */
  rule eq?(V1:Atm, V2:Atm) => t   requires V1 ==K  V2
  rule eq?(V1:Atm, V2:Atm) => nil requires V1 =/=K V2
  
  
  
  /* Transition rules for configurations (page 19) */
  
  /* <init : a, a1> */
  rule <actor>
         <k> initbeh(A1, V:Val) => nil ... </k>
         <id> A </id>
       </actor>
       <actor>
         <k> uninit(A) => ready(V) ... </k>
         <id> A1 </id>
       </actor>
  
  /* <new : a, a1> */
  rule <actor>
         <k> newadr() => !A1:Id ... </k>
         <id> A </id>
       </actor>
       (.Bag => <actor>
                  <k> uninit(A) </k>
                  <id> !A1 </id>
                </actor>)
       <definedaddr> Ads => Ads ListItem(!A1) </definedaddr>

  /* <send : a, m> */
  rule <actor>
         <k> send(V0:Val, V1:Val) => nil ... </k>
         <id> A </id>
       </actor>
       <messages>
         .List => ListItem( msg(V0, V1) ) ...
       </messages>
  
endmodule

































