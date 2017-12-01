/* A Formal Semantics for an Actor Language.
 * Reference: Gul Agha et al, A Foundation for Actor Computation, 1997
 */

require "substitution.k"

module ACTOR-SYNTAX

  imports SUBSTITUTION
  
  /* Values are terms that cannot rewrite anymore.
   * There are some main sub-categories of values.
   * Atoms are values that can be checked whether equal or not.
   * Comminication values are values that can be received in messages.
   */
  
  /* Atoms */  
  syntax Atm  ::= Int
                | "t"    // the boolean true  in our actor language
                | "nil"  // the boolean false in our actor language
  
  /* Communication values */
  syntax CVal ::= Atm
                | Id                            // variables
                | "pr" "(" CVal "," CVal ")"    // pairs of CVal
  
  /* Values */
  syntax Val  ::= CVal                                    
                | "lambda" "(" Id "," Exp ")" [binder]  // lambda abstraction
                | "pr" "(" Val "," Val ")"              // pairs of Val
  
  /* Call-by-value fixed-point combinator.
   * It is regarded as a value. We only unfold it once
   * when it is applied to an argument.
   */
  syntax Val  ::= "rec" "(" Exp ")"
  
  
  /* Expressions */
  
  syntax Exp  ::= Val   // values
  
  /* lambda application is evaluated from left to right (page 18) */
  syntax Exp  ::= "app" "(" Exp "," Exp ")" [seqstrict] // lambda application
  
  /* Expressions constructed with primitive operations (page 14) */
  syntax Exp  ::= "isatom"  "(" Exp                 ")" [seqstrict]
                | "isnat"   "(" Exp                 ")" [seqstrict]
                | "ispr"    "(" Exp                 ")" [seqstrict]
                | "br"      "(" Exp "," Exp "," Exp ")" [strict(1)]
                | "pr"      "(" Exp "," Exp         ")" [seqstrict]
                | "fst"     "(" Exp                 ")" [seqstrict]
                | "snd"     "(" Exp                 ")" [seqstrict]
                | "newadr"  "("                     ")" [seqstrict]
                | "initbeh" "(" Exp "," Exp         ")" [seqstrict]
                | "send"    "(" Exp "," Exp         ")" [seqstrict]
                | "become"  "(" Exp                 ")" [seqstrict]
                | "eq?"     "(" Exp "," Exp         ")" [seqstrict]
                
  /* Expressions that are syntactic sugar (page 15) */
  syntax Exp  ::= "if" "(" Exp "," Exp "," Exp ")" 
                | "let" "(" Binding "," Exp ")"
                | "seq" "(" Exp "," Exp ")"
                | "letactor" "(" Bindings "," Exp ")"

  /* Bindings and lists of bindings */
  syntax Binding  ::= "bind" "(" Id "," Exp ")"  // Id := Exp
  syntax Bindings ::= List{Binding, ","}

  /* Expressions constructed with user-defined functions. */
  syntax Exp ::= "mkset" "(" Exp ")"         [seqstrict]
               | "mkget" "(" Exp ")"         [seqstrict]
               | "set?"  "(" Exp ")"         [seqstrict]
               | "get?"  "(" Exp ")"         [seqstrict]
               | "cust"  "(" Exp ")"         [seqstrict]
               | "tree"  "(" Exp ")"         [seqstrict]
               | "left"  "(" Exp ")"         [seqstrict]
               | "right" "(" Exp ")"         [seqstrict]
               | "add"   "(" Exp "," Exp ")" [seqstrict]
               | "minus" "(" Exp "," Exp ")" [seqstrict]
               | "mult"  "(" Exp "," Exp ")" [seqstrict]
               | "le"    "(" Exp "," Exp ")" [seqstrict]
               
  /* Message */
  /* Messages are not syntactically restricted to be of the form
   * <Ad <= cV> (page 17).
   */
  syntax Message ::= "msg" "(" Val "," Val ")"  // < lhs <= rhs >
                   
  /* Actor states (page 16) */
  syntax AState  ::= "uninit" "(" Id  ")"            // (?a) uninitialized
                   | "ready"  "(" Val ")"            // (b)  ready to accept msg
                   | "exec"   "(" Exp ")"  [strict]  // [e]  busy executing e

  /* Meta-level information for rewriting strategies */
  syntax KVariable ::= Id
  syntax KResult   ::= Val
  
endmodule

module ACTOR

  imports ACTOR-SYNTAX
  
  syntax Id ::= "initactor" // the id of the initial actor

  configuration <T color="red">
                  <actors color="orange">
                    <actor multiplicity="*" color="yellow">
                      <k color="green"> exec($PGM:Exp) </k>
		      <id> initactor </id>
                    </actor>
                  </actors>
                  <messages>
                    <message  multiplicity="*">
                      .K
                    </message>
                  </messages>
                  <definedaddr> ListItem(initactor) </definedaddr>
                  <ext> .List </ext>
		  <recep> .List </recep>
                </T>
  
  /* Desugaring rules for syntactic sugar (page 15) */
  
  rule if(E0:Exp, E1:Exp, E2:Exp)
    => app(br(E0, lambda(!Z, E1), lambda(!Z, E2)), nil)
   
  rule let(bind(X:Id, E0:Exp), E1)
    => app(lambda(X, E1), E0)
    
  rule seq(E0:Exp, E1:Exp)
    => app(app(lambda(!Z, lambda(!X, !X)), E0), E1)
  
  /* letactor(bind(x1,e1),...,bind(xn,en), e)
   * => let(bind(x1,newadr()),
   *    let(bind(x2,newadr()),
   *    ...
   *    let(bind(xn,newadr()),
   *      seq(initbeh(x1,e1),
   *      seq(initbeh(x2,e2),
   *      ...
   *      seq(initbeh(xn,en), e))))))
   */
  rule letactor(BS:Bindings, E:Exp)
    => letactor-aux(BS:Bindings, E:Exp, BS:Bindings)
  
  /* letactor-aux is an auxiliary function that helps us rewrite letactor.
   * It makes two copies of the bindings and remembers them
   * in the first and third argument.
   * 
   * The first argument is for constructing nested let expressions.
   * The third argument is for constructing nested seq expressions.
   * 
   * The rules for letactor-aux are defined inductively on its first and 
   * third arguments.
   */
  syntax Exp ::= "letactor-aux" "(" Bindings "," Exp "," Bindings ")"
   
  rule letactor-aux(
         bind(X1:Id, E1:Exp), RestBS:Bindings,   // first arg is nonempty
         E:Exp,
         AllBS:Bindings)
    => let(bind(X1, newadr()),                   // construct let expression
         letactor-aux(RestBS, E, AllBS))
  
  rule letactor-aux(
         .Bindings,                              // first arg is empty
         E:Exp,
         bind(X1:Id, E1:Exp), RestBS:Bindings)   // third arg is nonempty
    => seq(initbeh(X1, E1),                      // construct seq expression
         letactor-aux(.Bindings, E, RestBS))
  
  rule letactor-aux(.Bindings, E:Exp, .Bindings) // both args are empty
    => E
         
  /* Reduction rules for the fixed-point combinator (I wrote it by myself) */
  
  rule app(rec(lambda(B:Id, E1:Exp)), E2:Exp)
    => app(subst(E1, rec(lambda(B, E1)), B), E2)
    
  syntax Exp ::= "subst" "(" Exp "," Exp "," Exp ")" // needed for parsing
  rule subst(K1, K2, K3) => K1 [ K2 / K3 ]

  /* Reduction rules of expressions (page 18) */
  
  /* (beta-v) */
  rule app(lambda(X:Id, E:Exp), V:Val) => E[V / X]
  
  /* (delta) rules are defined for each operators */
  rule add(  M:Int, N:Int)    => M +Int N
  rule minus(M:Int, N:Int)    => M -Int N
  rule mult( M:Int, N:Int)    => M *Int N
  rule le(   M:Int, N:Int)    => t        requires M <=Int N
  rule le(   M:Int, N:Int)    => nil      requires M >Int N
  /* See page 11. Messages are pairs of a tree and an address.
   * Trees are nested pairs.
   */
  rule tree(pr(Tree:Val, Cust:Val)) => Tree
  rule cust(pr(Tree:Val, Cust:Val)) => Cust
  rule left (Tree:Val)              => fst(Tree)
  rule right(Tree:Val)              => snd(Tree)
  
  /* (br) */
  rule br(nil  , V1:Val, V2:Val) => V2
  rule <k> br(V:Val, V1:Val, V2:Val) => V1 ... </k>
       <definedaddr> X </definedaddr>
    requires notBool((isId(V) andBool notBool(V in X)) orBool V ==K nil)
    // see page 18:
    // if v \in \mathcal{V} - ((\mathcal{X} - X) U {nil})
    
  /* (ispr) */
  rule ispr(V:Val) => t    requires isPairVal(V)
  rule <k> ispr(V:Val) => nil ... </k>
       <definedaddr> X </definedaddr>
    requires notBool((isId(V) andBool notBool(V in X)) orBool isPairVal(V))
    // see page 18:
    // if v \in \mathcal{V} - ((\mathcal{X} - X) U pr(\mathcal{V}, \mathcal{V}))
    
  syntax Bool ::= "isPairVal" "(" Val ")" [function]
  rule isPairVal(pr(V1:Val, V2:Val)) => true
  rule isPairVal(_)                  => false [owise]
  
  /* (fst) & (snd) */
  rule fst(pr(V1:Val, V2:Val)) => V1:Val
  rule snd(pr(V1:Val, V2:Val)) => V2:Val
  
  /* (eq) */
  rule eq?(V1:Atm, V2:Atm) => t   requires V1 ==K  V2
  rule eq?(V1:Atm, V2:Atm) => nil requires V1 =/=K V2
  
  
  
  /* Transition rules for configurations (page 19) */
  
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
       
       
  /* <init : a, a1> */
  rule <actor>
         <k> initbeh(A1, V:Val) => nil ... </k>
         <id> A </id>
       </actor>
       <actor>
         <k> uninit(A) => ready(V) ... </k>
         <id> A1 </id>
       </actor>
       
  /* <bec : a, a1> */
  rule <actor>
         <k> become(V:Val) => nil ... </k>
         <id> A => !A1:Id </id>
       </actor>
       (.Bag => <actor>
                  <k> ready(V) </k>
                  <id> A </id>
                </actor>)
       <definedaddr> Ads => Ads ListItem(!A1) </definedaddr>


  /* <send : a, m> */
  rule <actor>
         <k> send(V0:Val, V1:Val) => nil ... </k>
         <id> A </id>
       </actor>
       <messages>
         .Bag => <message> msg(V0, V1) </message>
         ...
       </messages>
  
  /* <rcv : a, cv> */
  rule <actor>
         <k> ready(V:Val) => exec(app(V, CV)) ... </k>
         <id> A </id>
       </actor>
       <messages>
         (<message> msg(A, CV:CVal) </message>) => .Bag
         ...
       </messages>
  
endmodule

































