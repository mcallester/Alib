
reinitialize();
/***  after 0 initialization;***/

/** ========================================================================
functions starts form initialization
========================================================================**/

//load_mode[0] = 1;

declare_package(`functions);
/***  {34;done}***/

clear_event(start_functions);
/***  the event start_functions is not present***/

define start_functions true;
/***  event 1 max_exps 0 net_exps 0 closures 0***/

exp_limit[0] = 100000;
/***  {35;done}***/

/** ========================================================================

========================================================================**/
define identity(sigma:type){lambda(x:sigma){x}};
/***  event 2 max_exps 73 net_exps 73 closures 97***/

define preimage(sigma:type, tau:type, y:tau, f:sigma=>tau){
  assert(x:sigma){f(x)=y}};
/***  event 3 max_exps 304 net_exps 304 closures 442***/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/***  event 4 max_exps 1084 net_exps 288 closures 1037***/

theorem injection_thm1 (tau:type,sigma:type,
			f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ 
  x_2=x_3}{
  classify(f(x_3)) //realize that f(x_3) has a unique preimage under f
  };
/***  event 5 max_exps 5551 net_exps 186 closures 6974***/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/***  event 6 max_exps 2475 net_exps 186 closures 1551***/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/***  event 7 max_exps 7089 net_exps 138 closures 4019***/

theorem bijections_invert(tau:type,sigma:type,f:bijection(sigma,tau)){
  exists(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}
  }{
  using(g =def lambda(x:tau){the(y:sigma){f(y)=x}}){
    show(x:sigma){g(f(x)) = x}; //backchaining from the goal and witness would do this
    witness(g)
    }};
/***  event 8 max_exps 10457 net_exps 504 closures 10672***/

theorem bij_inverses_unique(tau:type,sigma:type,f:bijection(sigma,tau)){
  unique(assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}})}{
  show(g1:assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}},
       g2:assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}){g1=g2}{
    show(y:tau){g1(y)=g2(y)}{
      using(x:preimage(y,f));};}
  };
/***  event 9 max_exps 13387 net_exps 26 closures 13158***/

define bij_inverse(tau:type,sigma:type,f:bijection(sigma,tau)){
  the(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}};
/***  event 10 max_exps 11437 net_exps 152 closures 7672***/

theorem bij_inverse_implementation(
				   tau:type,
				   sigma:type,
				   f:bijection(sigma,tau),
				   g1 =def lambda(y:tau){the(preimage(y,f))},
				   g2 =def bij_inverse(f)){
  g1 = g2}{
  show(y:tau){g1(y) = g2(y)} //should be immediate from backchaining.
  };
/***  event 11 max_exps 12655 net_exps 326 closures 12868***/

theorem bij_inverse_thm1(tau:type,sigma:type,f:bijection(sigma,tau)){
  is(bij_inverse(f),bijection)}{
  using(g =def lambda(y:tau){the(preimage(y,f))}){
    show(x:sigma){inhabited(preimage(x,g))}{classify(f(x))};
    witness(g)}
  };
/***  event 12 max_exps 16756 net_exps 101 closures 43366***/

theorem bij_preimage_thm(tau:type,sigma:type,f:bijection(sigma,tau),x:tau){
  inhabited(preimage(x,f)) && unique(preimage(x,f))};
/***  event 13 max_exps 13598 net_exps 153 closures 8931***/

define composition(sigma:type,tau:type,gamma:type,f:tau=>gamma,g:sigma=>tau){lambda(x:sigma){f(g(x))}};
/***  event 14 max_exps 15858 net_exps 281 closures 9856***/

define id_fun(s:type){lambda(x:s){x}};
/***  event 15 max_exps 7 net_exps 0 closures 26***/

theorem bij_inverse_thm2 (s:type,u:type,f:bijection(s,u)){
  composition(bij_inverse(f),f) = id_fun(s) && composition(f,bij_inverse(f)) = id_fun(u)};
/***  event 16 max_exps 21980 net_exps 1116 closures 17784***/

theorem bij_composition_thm (s:type, u:type, v:type, f:bijection(u,v), g:bijection(s,u)){
  is(composition(f,g),bijection)
  }{
  show(z:v){inhabited(preimage(z,composition(f,g)))}{
    using(pre1 =def the(preimage(z,f))){
      classify(pre1);
      witness(the(preimage(pre1,g)))}};
  show(z:v){unique(preimage(z,composition(f,g)))}{
    show(x1:preimage(z,composition(f,g)),
         x2:preimage(z,composition(f,g))){x1=x2}{
      show{g(x1)=g(x2)}}}
  };
/***  event 17 max_exps 69871 net_exps 1245 closures 111092***/

define permutation(sigma:type){bijection(sigma,sigma)};
/***  event 18 max_exps 12049 net_exps 112 closures 5638***/

theorem permutation_thm1 (s:type,f:permutation(s),g:permutation(s)){is(composition(f,g),permutation(s))};
/***  event 19 max_exps 4267 net_exps 322 closures 6514***/

theorem permutation_thm2(s:type,f:permutation(s)){composition(f,bij_inverse(f)) = id_fun(s)};
/***  event 20 max_exps 1453 net_exps 113 closures 3735***/

define associative(s:type){
  assert(f:s=>s=>s){
    forall(x:s,y:s,z:s){
      f(x,f(y,z))=f(f(x,y),z)}}};
/***  event 21 max_exps 3477 net_exps 436 closures 3577***/

define perm_composition(s:type,f:permutation(s),g:permutation(s)){composition(s,s,s,f,g)};//{lambda(x:s){f(g(x))}};
/***  event 22 max_exps 50954 net_exps 67 closures 31795***/

theorem composition_of_perms(s:type, p1:permutation(s), p2:permutation(s)){is(perm_composition(p1,p2), permutation(s))};
/***  event 23 max_exps 8115 net_exps 417 closures 12927***/

//needed to get the arrow type for op required in the next theorem
//permutation(s)=>(permutation(s)=>permutation(s))
theorem composition_of_perms2(s:type, p:permutation(s)){
  is(perm_composition(s,p), permutation(s)=>permutation(s))};
/***  event 24 max_exps 9730 net_exps 44 closures 14366***/

theorem composition_assoc_perms(s:type){is(perm_composition(s), associative(permutation(s)))}{ /*  */
  using(op =def perm_composition(s)){
    show(px:permutation(s),
	 py:permutation(s),
	 pz:permutation(s)){op(px,op(py,pz)) = op(op(px,py),pz)}}};
/***  event 25 max_exps 26522 net_exps 574 closures 55922***/

theorem id_is_a_perm(s:type){is(id_fun(s), permutation(s))};
/***  event 26 max_exps 1944 net_exps 224 closures 5855***/
