/* A Formal Semantics for an Actor Language.
 * Reference: Gul Agha et al, A Foundation for Actor Computation, 1997
 */

require "substitution.k"

module ACTOR-SYNTAX

  imports SUBSTITUTION
  
  /* Values are terms that cannot rewrite anymore.
   * There are some main sub-categories of values
   * which we introduce them here.
   * Atoms are values that can be checked whether equal or not.
   * Comminication values are values that can be received in messages.
   */
  
  /* Atoms (page 14) */  
  syntax Atm  ::= Int
                | "t"    // the boolean true  in our actor language
                | "nil"  // the boolean false in our actor language
  
  /* Communication values (page 17) */
  syntax CVal ::= Atm
                | Id                            // variables
                | "pr" "(" CVal "," CVal ")"    // pairs of CVal
  
  /* Values (page 14) */
  syntax Val  ::= CVal                                    
                | "lambda" "(" Id "," Exp ")" [binder]  // lambda abstraction
                | "pr" "(" Val "," Val ")"              // pairs of Val
  
  /* Call-by-value fixed-point combinator (page 9).
   * It is regarded as a value. We only unfold it once
   * when it is applied to an argument.
   */
  syntax Val  ::= "rec" "(" Exp ")"
  
  
  /* Expressions (page 15) */
  
  syntax Exp  ::= Val   // values
  
  /* lambda application is evaluated from left to right (page 18) */
  syntax Exp  ::= "app" "(" Exp "," Exp ")" [seqstrict] // lambda application
  
  /* Expressions constructed with primitive operations (page 14) */
  syntax Exp  ::= "isatom"  "(" Exp                 ")" [seqstrict]
                | "isnat"   "(" Exp                 ")" [seqstrict]
                | "ispr"    "(" Exp                 ")" [seqstrict]
                | "br"      "(" Exp "," Exp "," Exp ")" [seqstrict] // [strict(1)]
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

  /* Expressions constructed with user-defined functions.
   * All of them are evaluated from left to right (page 18)
   */
  syntax Exp ::= "mkset" "(" Exp ")"         [seqstrict]
               | "mkget" "(" Exp ")"         [seqstrict]
               | "set?"  "(" Exp ")"         [seqstrict]
               | "get?"  "(" Exp ")"         [seqstrict]
               | "cust"  "(" Exp ")"         [seqstrict]
               | "tree"  "(" Exp ")"         [seqstrict]
               | "left"  "(" Exp ")"         [seqstrict]
               | "right" "(" Exp ")"         [seqstrict]
               | "isnat" "(" Exp ")"         [seqstrict]
               | "add"   "(" Exp "," Exp ")" [seqstrict]
               | "minus" "(" Exp "," Exp ")" [seqstrict]
               | "mult"  "(" Exp "," Exp ")" [seqstrict]
               | "le"    "(" Exp "," Exp ")" [seqstrict]
               | "and"   "(" Exp "," Exp ")" [seqstrict]
               | "or"    "(" Exp "," Exp ")" [seqstrict]

  /* Actor states (page 16, 17) */
  syntax AState  ::= "uninit" "(" Id  ")"            // (?a) uninitialized
                   | "ready"  "(" Val ")"            // (b)  ready to accept msg
                   | "exec"   "(" Exp ")"  [strict]  // [e]  busy executing e
                   
  /* Message */
  /* Messages are not syntactically restricted to be of the form
   * <Ad <= cV> (page 17).
   */
  syntax Message ::= "msg" "(" Val "," Val ")"  // < lhs <= rhs >

  /* Meta-level information */
  syntax KVariable ::= Id   // for binding (in lambda abstraction)
  syntax KResult   ::= Val  // for rewriting strategy
  
endmodule

module ACTOR

  imports ACTOR-SYNTAX
  
  syntax Id ::= "initactor" // the id of the initial actor

  /* Actor configuration (page 17) */
  configuration <T>
                  <actors>
                    <actor multiplicity="*">     // a multiset of actors
                      <k> exec($PGM:Exp) </k>    // actor state
		      <id> initactor </id>       // actor id
                    </actor>
                  </actors>
                  <messages>
                    <message  multiplicity="*">  // a multiset of messages
                      .K
                    </message>
                  </messages>
                  <definedaddr>                  // list of defined actors'
                    ListItem(initactor)          // addresses
                  </definedaddr>
                  // <ext> .List </ext>          // external actors
		  // <recep> .List </recep>      // receptionists
                </T>

  
  /* Desugaring rules for syntactic sugar (page 15) */
  
  rule if(E0:Exp, E1:Exp, E2:Exp)
    => app(br(E0, lambda(!Z, E1), lambda(!Z, E2)), nil) // !Z fresh
   
  rule let(bind(X:Id, E0:Exp), E1:Exp)
    => app(lambda(X, E1), E0)
    
  rule seq(E0:Exp, E1:Exp)
    => app(app(lambda(!Z, lambda(!X, !X)), E0), E1)     // !X fresh
  
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
    
         
  /* Reduction rules for the fixed-point combinator (not in paper) */
  
  rule app(rec(lambda(B:Id, E1:Exp)), E2:Exp)
    => app(subst(E1, rec(lambda(B, E1)), B), E2)
    
  syntax Exp ::= "subst" "(" Exp "," Exp "," Exp ")" // needed for parsing
  rule subst(K1, K2, K3) => K1 [ K2 / K3 ]  // reduce to builtin substitution

  /* Reduction rules of expressions (page 18) */
  
  /* (beta-v) */
  rule app(lambda(X:Id, E:Exp), V:Val) => subst(E, V, X)
  
  /* (delta) rules are defined for each functions */
  rule add  (M:Int, N:Int)    => M +Int N
  rule minus(M:Int, N:Int)    => M -Int N
  rule mult (M:Int, N:Int)    => M *Int N
  rule le   (M:Int, N:Int)    => t        requires M <=Int N
  rule le   (M:Int, N:Int)    => nil      requires M >Int N

  rule and(nil, V:Val) => nil
  rule and(t  , V:Val) => V
  rule or (t  , V:Val) => t
  rule or (nil, V:Val) => V

  /* User-defined functions for the example of tree production (page 11).
   * In that example, messages are pairs of a tree and a customer actor address.
   * Trees are implemented as nested pairs.
   */
  rule tree(pr(Tree:Val, Cust:Val)) => Tree // get the "tree" field of a message
  rule cust(pr(Tree:Val, Cust:Val)) => Cust // get the "cust" field of a message
  rule left (Tree:Val)              => fst(Tree) // get the left subtree
  rule right(Tree:Val)              => snd(Tree) // get the right subtree
  rule isnat(M:Int)                 => t
  rule isnat(pr(V1:Val, V2:Val))    => nil
  
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
  
  /* <fun : a> is obtained for free by using K's strictness attributes. */
  
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

  /* Alternatively:
   * rule <actor>
   *        <k> (become(V:Val) ~> RestComputation) => ready(V) </k>
   *        ...
   *      </actor>
   *      (.Bag => <actor>
   *                 <k> nil ~> RestComputation </k>
   *                 <id> !A1:Id </id>
   *               </actor>)
   *      <definedaddr> Ads => Ads ListItem(!A1) </definedaddr>
   */


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
