module EQUALITY-SPEC
  imports ACTOR
  
  rule
    <actors>
      <actor>
        <k>
          letactor(
            bind(#parseToken("Id@ACTOR-SYNTAX", "test"), rec(lambda(y, lambda(x, seq(send(x,5),become(y)))))),
            send(test, initactor))
          =>
          nil ...
        </k>
        <id> initactor </id>
      </actor>
      (.Bag => _)
    </actors>

endmodule
