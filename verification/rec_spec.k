module REC-SPEC
  imports ACTOR
  
  rule
    <actors>
      <actor>
        <k>
          letactor(
            bind(#id("test"), rec(lambda(#id("y"), lambda(#id("x"), seq(send(#id("x"),5),become(#id("y"))))))),
            send(#id("test"), #id("initactor")))
          =>
          nil ...
        </k>
        <id> #id("initactor") </id>
      </actor>
      (.Bag => _)
    </actors>

endmodule
