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

    //todo!
    ghost function Valid() : bool 

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