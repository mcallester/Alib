restart_event(`caley);

declare_package(`caley);

define associative(s:set,f:s=>s=>s){
  forall(x:s,y:s,z:s){f(x,f(y,z)) = f(f(x,y),z)}
  };

define surjective(s:set,w:set,f:s=>w){
  forall(y:w){exists(x:s){f(x)=y}}
    };
    
define surjection(s:set){
  assert(f:s=>s){surjective(s,s,f)}
  };

define other_than(s:set,x:s){
  assert(y:s){not(y=x)}
  };

define injective(s:set,w:set,f:s=>w){
  forall(x:s,y:other_than(s,x)){not(f(y) = f(x))}
    };
    
define injection(s:set){
  assert(f:s=>s){surjective(s,s,f)}
  };

class group () {
  member:set,
  op:member=>member=>member,
  associative(member,op),
  id:member,
  forall(x:member){op(id,x) = x && op(x,id) = x},
  inv:member=>member,
  forall(x:member){op(x,inv(x)) = id && op(inv(x),x) = id}
  };

define composition(s:set,u:set,w:set,f:s=>u,g:u=>w){
  lambda(x:s){g(f(x))}
  };

    

class naked_set () {member:set};

define the_subtype(s:set,P:s=>bool){
  obj(naked_set,member=assert(x:s){P(x)})
  };

define caley_bijection(G:group,x:G.member){
  lambda(y:G.member){G.op(x,y)}
  };

define permutation(s:set,assert(f:s=>s){
define caley_bijections(G:group){
  the_subtype(f:permutation(G.member),
	      lambda(f:permutation(G.member)){
		exists(x:G.member){
		  f = caley_bijection(G,x)}})
  }

define caley_group(G:group){
  obj(group,
      member = caley_bijections.member
      op = restrict(composition(G.member,G.member,G.member),member)
      inv = restrict(bij_inverse(G.member),member)
      id = lambda(f:member){f})
  }

define caley_isomorphism(G:group){
  lambda(x:G.member){caley_bijection(G,x)}
  }

theorem caley (G:group){
  Apply_iso(caley_isomorphism(G),G) = caley_group(G)}


