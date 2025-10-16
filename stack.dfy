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
      ensures Valid()
      ensures this.content == [ v ]
      ensures this.footprint == { this } 
    {
      this.val := v;
      this.next := null;
      this.footprint := { this };
      this.content := [ val ];
    }

    //Adds to the end of the list
    method add(v: int) returns (r : Node)
      requires Valid()
      ensures Valid()
      ensures fresh(this.footprint - old(this.footprint))
      ensures this.footprint >= old(this.footprint)
      ensures this.content == old(this.content) + [v]
      modifies this, footprint
      decreases footprint
    {
      var node;
      if (this.next == null) {
        node := new Node(v);
        this.next := node;
      } else {
        node := this.next.add(v);
      }
      this.footprint := { this } + this.next.footprint;
      this.content := [ this.val ] + this.next.content;
      return node;
    }
    
    method mem(v: int) returns (b : bool)
      requires Valid()
      ensures Valid()
      ensures b <==> v in this.content
      decreases footprint
    {
      if (this.val == v) {
        b := true;
      } else if (this.next != null) {
        b := this.next.mem(v);
      } else {
        b := false;
      }
    }
    
    method remove() returns (empty: bool, v: int)
      requires Valid()
      ensures Valid()
      ensures old(this.next) == null <==> empty
      ensures v == old(this.content[|this.content|-1])
      ensures old(this.next) != null ==> old(this.content) == this.content + [ v ]
      ensures this.next != null ==> old(this.next) != null
      ensures this.next != null ==> this.next.footprint <= old(this.next.footprint)
      modifies this, footprint
      decreases footprint
    {
      if (this.next == null) {
        return true, this.val;
      } else {
        var empty, v := this.next.remove();
        if (empty) {
          this.next := null;
          this.footprint := { this };
          this.content := [ this.val ];
        } else {
          this.footprint := { this } + this.next.footprint;
          this.content := [ this.val ] + this.next.content;
        }
        return false, v;
      }
    }
}

class Stack {
    var head : Node?

    ghost var footprint : set<object>
    ghost var content : seq<int> 

    ghost function Valid() : bool
      reads this, this.footprint
      decreases footprint
    {
      this in this.footprint
      &&
      if (this.head == null)
        then
          this.footprint == { this }
          && 
          this.content == []
        else
          this.head in this.footprint
          &&
          this.head.footprint <= this.footprint
          &&
          this.head.Valid()
          &&
          this.footprint == { this, this.head } + this.head.footprint
          &&
          this.content == this.head.content
          &&
          this.content != []
    }

    constructor ()
      ensures Valid()
      ensures this.content == []
      ensures this.footprint == {this}
      ensures fresh(footprint)
    {
      this.head := null;
      this.footprint := { this };
      this.content := [];
    }
    

    function  isEmpty() : bool
      reads this, this.footprint
      requires Valid()
      ensures Valid()
      ensures this.isEmpty() <==> this.content == []
      ensures this.isEmpty() <==> this.footprint == { this }
    {
      this.head == null
    }


    method push(v: int)
      requires Valid()
      ensures Valid()
      ensures this.content == old(this.content) + [ v ]
      ensures fresh(this.footprint - old(this.footprint))
      ensures this.footprint >= old(this.footprint)
      modifies this, footprint
    {
      if (this.head == null) {
        this.head := new Node(v);
        this.content := this.content + [ v ];
        this.footprint := { this, this.head } + this.head.footprint;
      } else {
        var _ := this.head.add(v);
        this.content := this.content + [ v ];
        this.footprint := { this, this.head } + this.head.footprint;
      }
    }

    // TODO: check pre- and post-conditions
    method pop() returns (r: int)
      requires Valid()
      requires !this.isEmpty()
      ensures Valid()
      ensures old(this.content) == this.content + [ r ]
      ensures this.footprint <= old(this.footprint)
      modifies this, footprint
    {
      var empty, v := this.head.remove();
      if (empty) {
        this.head := null;
        this.footprint := { this };
        this.content := [];
      } else {
        this.content := this.head.content;
        this.footprint := { this, this.head } + this.head.footprint;
      }
      return v;
    }
}

method example() {
  var stack := new Stack();
  // var a := stack.pop(); // error
  stack.push(123);
  var b := stack.pop();
  if (!stack.isEmpty()) {
    var c := stack.pop();
    stack.push(456);
    assert !stack.isEmpty();
    if (!stack.isEmpty()) {
      var c := stack.pop();
    }
  }
}
