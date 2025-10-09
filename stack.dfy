class Node {

    var val : int
    var next : Node?

    ghost var footprint : set<Node>
    ghost var content : seq<int> 

    ghost function Valid() : bool 
      reads this, this.footprint 
      decreases footprint
    {
      this in this.footprint 
      &&
      if (this.next == null)
        then 
          this.footprint == { this }
          && 
          this.content == [this.val]
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == [this.val] + this.next.content
          &&
          this.next.Valid()
    }

    constructor (v : int)
    ensures Valid() //&& //add more here!
    



    //Adds to the end of the list
    method add(v : nat) returns (r : Node)
    
    

    method mem(v : nat) returns (b : bool)


}

class Stack {
    var head : Node?

    ghost var footprint : set<object>
    ghost var content : seq<int> 

    ghost predicate NodeMatchesContent(node: Node?, i: nat)
      requires i <= |content|
      // allow reading the stack's ghost state and all nodes inside footprint:
      reads this`content, this`footprint, set n | n in this.footprint
      decreases |content| - i
    {
      if node == null then
        i == |content|
      else if i == |content| then
        node == null
      else
        node in footprint && node.val == content[i] && NodeMatchesContent(node.next, i+1)
    }

    //todo!
    ghost function Valid() : bool
    {
      NodeMatchesContent(head, 0)
    }

    constructor ()
    ensures Valid() && this.content == [] && this.footprint == {this}
    ensures fresh(footprint)
    

    function  isEmpty() : bool
    //Add a specification here!


    method push(v:int)
    requires Valid()
    ensures Valid() //&& //add more here!

    method pop() returns (r:int)
    requires Valid()
    ensures Valid() //&& //add more here!
}