restart_event(`caley);
/** {30;done} **/

declare_package(`caley);
/** {31;done} **/

define associative(s:set,f:s=>s=>s){
  forall(x:s,y:s,z:s){f(x,f(y,z)) = f(f(x,y),z)}
  };
/** {32;done} **/

define surjective(s:set,w:set,f:s=>w){
  forall(y:w){exists(x:s){f(x)=y}}
    };
/** {33;done} **/
    
define surjection(s:set){
  assert(f:s=>s){surjective(s,s,f)}
  };
/** {34;done} **/

define other_than(s:set,x:s){
  assert(y:s){not(y=x)}
  };
/** {35;done} **/

define injective(s:set,w:set,f:s=>w){
  forall(x:s,y:other_than(s,x)){not(f(y) = f(x))}
    };
/** {36;done} **/
    
define injection(s:set){
  assert(f:s=>s){surjective(s,s,f)}
  };
/** {37;done} **/

define permutation(s:set){
  assert(f:s=>s){is(f,injection(s)) && is(f,surjection(s))}
  };
/** {38;done} **/
		     
class group () {
  member:set,
  op:member=>member=>member,
  associative(member,op),
  id:member,
  forall(x:member){op(id,x) = x && op(x,id) = x},
  inv:member=>member,
  forall(x:member){op(x,inv(x)) = id && op(inv(x),x) = id}
  };
/** {39;done} **/

define composition(s:set,u:set,w:set,f:s=>u,g:u=>w){
  lambda(x:s){g(f(x))}
  };
/** {40;done} **/

class naked_set(){member:set};
/** {41;done} **/

define the_subtype(s:set,P:s=>bool){
  obj(naked_set,member=assert(x:s){P(x)})
  };
/** {42;done} **/

define caley_bijection(G:group,x:G.member){
  lambda(y:G.member){G.op(x,y)}
  };
/** {43;done} **/


define caley_set(G:group){
  the_subtype(permutation(G.member),
	      lambda(f:permutation(G.member)){
		exists(x:G.member){f = caley_bijection(G,x)}})
  };
/** {44;done} **/

define caley_group(G:group){
  obj(group,
      member = caley_set.member
      op = lambda(f:member,g:member){composition(member,member,member,f,g)},
      inv = lambda(f:member){inverse(member,f)},
      id = lambda(f:member){f})
  };
/** {
    in context;
    G:group;
    f:G.member;
    undefined symbol inverse} **/

theorem(G:group){
  lemma{is(caley_bijection(G),
	   isomorphism(G,caley_group(G)))}
  isomorphic(G,caley_goup(G))
  }


