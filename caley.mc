class group {
  member:set,
  op:element->element->element,
  inv:element->element,
  id:element,...}

//this class definition takes an argument and has no parents.

define composition(s:set,u:set,w:set,f:s->u,g:u->w){
  lambda(x:s){g(f(x))}
  }

define subtype(tau:set){
  class{P:tau->bool,member:assert{x:tau}{P(x)}}
  }

define the_subype(s:set,P:s->bool){
  obj(subtype,s=set,P=P)
  }

define caley_bijection(G:group,x:G.member){
  lambda(y:G.member)G.op(x,y)}

define caley_bijections(G:group){
  the_subtype(f:permutation(G.member),
	      lambda(f:perumtation(G.member)){
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


