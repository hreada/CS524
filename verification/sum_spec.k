module SUM-SPEC
  imports ACTOR
  
  rule
    <actors>
      <actor>
        <k> app(rec(lambda(#id("sum"), lambda(#id("n"),
                  if(eq?(#id("n"), 0), 0, add(app(#id("sum"), minus(#id("n"), 1)), #id("n")))))),
                minus(5, 1))
            => (5 *Int (5 -Int 1)) /Int 2 ...
        </k>
        <id> initactor </id>
      </actor>
    </actors>
    // requires X >Int 2

endmodule
