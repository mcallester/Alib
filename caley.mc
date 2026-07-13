clear_event(initialization);
/** initialization and following events have been removed **/

where();
/** {
    pre-initialization;
    you can compile code here and then call initialize();} **/

initialize();
/** {33;done} **/

declare_package(`caley);
/** {34;done} **/


/** ========================================================================
group definition
========================================================================**/

class naked_set {member:type};
/** {35;done} **/

class magma (naked_set){op:member=>member=>member};
/** {36;done} **/

define associative(tau:type){
  assert(f:tau=>tau=>tau){
    forall(x,y,z:tau){f(x,f(y,z)) = f(f(x,y),z)}}};
/** {37;done} **/

class semigroup (magma){is(op,associative)};
/** {38;done} **/

class group (semigroup){
  id:member, forall(x:member){op(id,x) = x && op(x,id) = x},
  inv:member=>member, forall(x:member){op(inv(x),x) = id && op(x,inv(x)) = id}};
/** {39;done} **/

/** ========================================================================
The caley group
========================================================================**/

define comp(s:type,u:type,v:type,f:u=>v,g:s=>u){lambda(x:s){f(g(x))}};
/** {40;done} **/

int_exp(max_total[0])
/** {41;11359} **/

intern_stepping[0] = 1;
/** {42;done} **/

define permutation(s:type){assert(f:s=>s){is(f,bijection)}};
/**  **/
