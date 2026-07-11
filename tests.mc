clear_event(initialization);
/** initialization and following events have been removed **/

where();
/** {
    pre-initialization;
    you can compile code here and then call initialize();} **/

initialize();
/** {35;done} **/

declare_package(`test);
/** {36;done} **/

/** ========================================================================
test of type inference
========================================================================**/

intern_stepping[0] = 0;
/** {37;done} **/

define apply(s:type,g:s=>s,x:s){g(x)};
/** apply is a reserved name **/

define app(s:type,g:s=>s,x:s){g(x)};
/** {38;done} **/

intern_stepping[0] = 1;
/** {39;done} **/

clear_event(h);
/** the event h is not present **/

define h(s:type,g:s=>s,x:s){app(g,x)};
/** {
    1.in h;
    2.intern_decl(s:type);
    3.intern_decl(g:arrow(s,s));
    4.intern_decl(x:s);
    5.returning lambda(bound_x:s){app(s,g,bound_x)};
    6.BREAKPOINT;} **/

finish_event();
/** {40;done} **/

intern_stepping[0] = 0;
/** {41;done} **/

define associative(tau:type){
  assert(f:tau=>tau=>tau){
    forall(x,y,z:tau){f(x,f(y,z)) = f(f(x,y),z)}}};
/** {42;done} **/

intern_stepping[0] = 1;
/** {43;done} **/

define is_associative(s:type,f:s=>s=>s){is(f,associative)};
/** {
    1.in is_associative;
    2.intern_decl(s:type);
    3.intern_decl(f:arrow(s,arrow(s,s)));
    4.returning lambda(bound_fun:arrow(s,arrow(s,s))){
      is(bound_fun,associative(s))};
    5.BREAKPOINT;} **/

finish_event();
/** {44;done} **/

/** ========================================================================
a test of unnormalize
========================================================================**/

sugar_noname(intern_exp(`associative))
/** {
    45;
    lambda(bound_s:type){
      assert(bound_fun:arrow(bound_s,
                             arrow(bound_s,bound_s))){
        forall(bound_x:bound_s,
               bound_x_2:bound_s,
               bound_x_3:bound_s){
          equal(bound_fun(bound_x,
                          bound_fun(bound_x_2,bound_x_3)),
                bound_fun(bound_fun(bound_x,bound_x_2),
                          bound_x_3))}}}} **/

intern_stepping[0] = 1;
/** {46;done} **/

define foo(s:type){associative(s)};
/** {
    1.in foo;
    2.intern_decl(s:type);
    3.returning lambda(bound_s:type){associative(bound_s)};
    4.BREAKPOINT;} **/

class_of(associative(s))
/** {
    47;
    1:[_ associative(s)_];
    2:associative(s);} **/

finish_event();
/** {47;done} **/


/** ========================================================================
from Schoedrer-Bernstein
========================================================================**/

intern_stepping[0] = 0;
/** {48;done} **/

clear_event(preimage);
/** the event preimage is not present **/

where();
/** {1.after foo;} **/

define preimage(tau:type, sigma:type, y:sigma, h:tau=>sigma){
  assert(x:tau){h(x)=y}};
/** {49;done} **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** {50;done} **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** {51;done} **/

clear_event(bijection);
/** the event bijection is not present **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection) && is(f,surjection)}};
/** {52;done} **/


/** ========================================================================
objects
========================================================================**/
clear_event (magma);
/** the event magma is not present **/

where();
/** {1.after bijection;} **/

class magma{member:type,op:member=>member=>member};
/** {57;done} **/

sugar_noname(intern_exp(`magma))
/** {
    58;
    class(emptyobj){
      member:type;
      op:arrow(bound_Obj.member,
               arrow(bound_Obj.member,
                     bound_Obj.member))}} **/

class naked_set {member:type};
/** {59;done} **/

class magma2{member:type,op:member=>member=>member};
/** {60;done} **/

sugar_noname(intern_exp(`magma))
/** {
    65;
    class(naked_set){
      op:arrow(bound_Obj.member,
               arrow(bound_Obj.member,
                     bound_Obj.member))}} **/

sugar(intern_exp(`magma))
/** {66;magma3} **/

class magma3(naked_set){op:member=>member=>member};
/** {63;done} **/

sugar_noname(intern_exp(`magma))
/** {
    64;
    class(naked_set){
      op:arrow(bound_Obj.member,
               arrow(bound_Obj.member,
                     bound_Obj.member))}} **/

sugar(intern_exp(`magma))
/** {65;magma3} **/

class semigroup (magma){is(op,associative)};
/** {66;done} **/

clear_event(group);
/** group and following events have been removed **/

class group (semigroup){
  id:member, forall(x:member){op(id,x) = x && op(x,id) = x},
  inv:member=>member, forall(x:member){op(inv(x),x) = id && op(x,inv(x)) = id}};
nn/** {67;done} **/
