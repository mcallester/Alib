
reinitialize();
/** after 0 initialization; **/

/** ========================================================================
functions starts form initialization
========================================================================**/

//load_mode[0] = 1;

declare_package(`functions);

clear_event(start_functions);
/** the event start_functions is not present **/

define start_functions true;
/** event 1 max 0 net 0 **/

/** ========================================================================

========================================================================**/
define identity(sigma:type){lambda(x:sigma){x}};
/** event 2 max 120 net 120 **/

define preimage(sigma:type, tau:type, y:tau, f:sigma=>tau){
  assert(x:sigma){f(x)=y}};
/** event 3 max 2050 net 2050 **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** event 4 max 2197 net 2197 **/

theorem injection_thm1 (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ 
  x_2=x_3}{
  classify(f(x_3)) //realize that f(x_3) has a unique preimage under f
  };
/** event 5 max 4657 net 1069 **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** event 6 max 4082 net 1552 **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** event 7 max 5187 net 888 **/

clear_event(bijections_invert);
/** the event bijections_invert is not present **/

theorem bijections_invert(tau:type,sigma:type,f:bijection(sigma,tau)){
  exists(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}
  }{
  using(g = lambda(x:tau){the(y:sigma){f(y)=x}}){
    //    show(x:sigma){g(f(x)) = x};
    witness(g)
    }};
/** event 8 max 14568 net 2336 **/

clear_event(bij_inverses_unique);
/** the event bij_inverses_unique is not present **/

theorem bij_inverses_unique(tau:type,sigma:type,f:bijection(sigma,tau)){
  unique(assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}})
  } {
  show(g1:assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}},
       g2:assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}){g1=g2}{
    show(y:tau){g1(y)=g2(y)}{
      using(x:preimage(y,f));};};
  };
/** event 9 max 27230 net 116 **/

clear_event(bij_inverse);
/** the event bij_inverse is not present **/

define bij_inverse(tau:type,sigma:type,f:bijection(sigma,tau)){
  the(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}};
/** event 10 max 7416 net 924 **/

clear_event(bij_inverse_implementation);
/** the event bij_inverse_implementation is not present **/

theorem bij_inverse_implementation(tau:type,sigma:type,f:bijection(sigma,tau)){
  bij_inverse(f)=lambda(y:tau){the(preimage(y,f))}}{
  witness(lambda(y:tau){the(preimage(y,f))})
  };
/** event 11 max 18290 net 2357 **/

//applications_of(bij_inverse(f))

clear_event(bij_inverse_thm1);
/** the event bij_inverse_thm1 is not present **/
proof_stepping[0]=0;
theorem bij_inverse_thm1(tau:type,sigma:type,f:bijection(sigma,tau)){
  is(bij_inverse(f),bijection)}{
  using(g=lambda(y:tau){the(preimage(y,f))}){
    show(x:sigma){inhabited(preimage(x,g))}{classify(f(x))};
    witness(g)}
  };
/** event 12 max 21655 net 539 **/

theorem bij_preimage_thm(tau:type,sigma:type,f:bijection(sigma,tau),x:tau){
  inhabited(preimage(x,f)) && unique(preimage(x,f))};
/** event 13 max 10320 net 799 **/

define composition(sigma:type,tau:type,gamma:type,f:tau=>gamma,g:sigma=>tau){lambda(x:sigma){f(g(x))}};
/** event 14 max 30014 net 30014 **/

define id_fun(s:type){lambda(x:s){x}};
/** event 15 max 7 net 0 **/

clear_event(bij_inverse_thm2);
/** the event bij_inverse_thm2 is not present **/

theorem bij_inverse_thm2 (s:type,u:type,f:bijection(s,u)){
  composition(bij_inverse(f),f) = id_fun(s) && composition(f,bij_inverse(f)) = id_fun(u)};
/** event 16 max 33787 net 10345 **/

clear_event(bij_composition_thm);
/** the event bij_composition_thm is not present **/

theorem bij_composition_thm (s:type, u:type, v:type, f:bijection(u,v), g:bijection(s,u)){
  is(composition(f,g),bijection)
  }{
  show(z:v){inhabited(preimage(z,composition(f,g)))}{
    using(pre1 = the(preimage(z,f))){
      classify(pre1);
      witness(the(preimage(pre1,g)))}};
  
  show(z:v){unique(preimage(z,composition(f,g)))}{
    show(x1:preimage(z,composition(f,g)),
         x2:preimage(z,composition(f,g))){x1=x2}{
      classify(g(x2)); classify(g(x1))}}};
/** event 17 max 99866 net 68821 **/

clear_event(permutation);
/** the event permutation is not present **/

define permutation(sigma:type){bijection(sigma,sigma)};
/** event 18 max 131 net 130 **/

theorem permutation_thm1 (s:type,f:permutation(s),g:permutation(s)){is(composition(f,g),permutation(s))};
/** event 19 max 14502 net 559 **/

theorem permutation_thm2(s:type,f:permutation(s)){composition(f,bij_inverse(f)) = id_fun(s)};
/** event 20 max 8188 net 200 **/

clear_event(associative);
/** the event associative is not present **/

define associative(s:type){
  assert(f:s=>s=>s){
    forall(x:s,y:s,z:s){
      f(x,f(y,z))=f(f(x,y),z)}}};
/** event 21 max 11837 net 2998 **/

clear_event(perm_composition);
/** the event perm_composition is not present **/
define perm_composition(s:type,f:permutation(s),g:permutation(s)){composition(s,s,s,f,g)};//{lambda(x:s){f(g(x))}};
/** event 22 max 18706 net 201 **/

clear_event(composition_of_perms);
/** the event composition_of_perms is not present **/

theorem composition_of_perms(s:type, p1:permutation(s), p2:permutation(s)){is(perm_composition(p1,p2), permutation(s))};
/** event 23 max 19338 net 2462 **/

//needed to get the arrow type for op required in the next theorem
//permutation(s)=>(permutation(s)=>permutation(s))
theorem composition_of_perms2(s:type, p:permutation(s)){
  is(perm_composition(s,p), permutation(s)=>permutation(s))};
/** event 24 max 19905 net 141 **/

clear_event(composition_assoc_perms);
/** the event composition_assoc_perms is not present **/

theorem composition_assoc_perms(s:type){is(perm_composition(s), associative(permutation(s)))}{ /*  */
  using(op = perm_composition(s)){
    show(px:permutation(s),
         py:permutation(s),
         pz:permutation(s)){op(px,op(py,pz)) = op(op(px,py),pz)}}};
/** event 25 max 41532 net 2014 **/

clear_event(id_is_a_perm);
/** the event id_is_a_perm is not present **/

theorem id_is_a_perm(s:type){is(id_fun(s), permutation(s))}{
  //show(z:s){unique(preimage(z,id_fun(s)))};
  //show(z:s){inhabited(preimage(z,id_fun(s)))};
  classify(id_fun(s))};
/** event 26 max 53972 net 915 **/


// revise funp classification
