
/** ========================================================================
Algbra requires functions
========================================================================**/

load_mode[0] = 1; 
/** {36;done} **/

declare_package(`algebra);
/** {37;done} **/

clear_event(start_algebra); 
/** the event start_algebra is not present **/

define start_algebra true; 
/** event 17 max 0 net 0 **/

/** ========================================================================
group definition
========================================================================**/

class naked_set {member:type};
/** event 18 max 18 net 16 **/

class magma (naked_set){op:member=>member=>member};
/** event 19 max 59 net 59 **/

class semigroup (magma){is(op,associative)};
/** event 20 max 1173 net 1173 **/

class group (semigroup){
  id:member;
  forall(x:member){op(id,x) = x && op(x,id) = x};
  inv:member=>member;
  forall(x:member){op(inv(x),x) = id && op(x,inv(x)) = id}};
/** event 21 max 767 net 767 **/

