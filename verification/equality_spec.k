module EQUALITY-SPEC
  imports ACTOR
  
  rule
    <actors>
      <actor>
        <k> eq?(X:Int, X:Int) => t ... </k>
        <id> initactor </id>
      </actor>
    </actors>

endmodule
