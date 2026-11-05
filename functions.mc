initialize();

/** ========================================================================
functions starts form initialization
========================================================================**/

declare_package(`functions);

clear_event(start_functions);

break_on_user_error[0] = 1;

define start_functions true;

where();

exp_limit[0] = 100000;

/** ========================================================================

========================================================================**/

define id_fun(sigma:type){lambda(x:sigma){x}};
/***  event 2 max_exps 96 net_exps 96 rules 313***/

define preimage(sigma:type;tau:type;y:tau; f:sigma=>tau){x:sigma:f(x)=y};
/***  event 3 max_exps 854 net_exps 854 rules 3660***/

define injection(tau:type;sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/***  event 4 max_exps 2182 net_exps 265 rules 4470***/

define surjection(tau:type;sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/***  event 5 max_exps 2600 net_exps 106 rules 4380***/

define bijection(tau:type;sigma:type){
  assert(f:tau=>sigma){is(f,injection) && is(f,surjection)}};
/***  event 6 max_exps 2609 net_exps 176 rules 5035***/

clear_event(bijections_invert);
/***  after 6 bijection;***/

theorem bijections_invert(tau:type;sigma:type;f:bijection(sigma,tau)){
  exists(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}
  }{
  witness(lambda(y:tau){the(x:sigma){f(x)=y}})};
/***  event 7 max_exps 4204 net_exps 1084 rules 21469***/

theorem bij_inverses_unique   (tau:type; sigma:type; f:bijection(sigma,tau)){
  unique(g:tau=>sigma : forall(x:sigma){g(f(x))=x})
  }{
  show(
       g1:tau=>sigma: forall(x:sigma){g1(f(x))=x};
       g2:tau=>sigma:forall(x:sigma){g2(f(x))=x}){
    g1 = g2
    }{
    show(y:tau){g1(y)=g2(y)}{
      using(x:sigma:y=f(x))}}
  };
/***  event 8 max_exps 10476 net_exps 131 rules 138968***/

define bij_inverse(
		   tau:type;
		   sigma:type;
		   f:bijection(sigma,tau)){
  the(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}};
/***  event 9 max_exps 5928 net_exps 636 rules 20243***/

clear_event(bij_inverse_implementation);
/***  after 9 bij_inverse;***/

theorem bij_inverse_implementation(
				   tau:type;
				   sigma:type;
				   f:bijection(sigma,tau);
				   g1 =def lambda(y:tau){the(preimage(y,f))};
				   g2 =def bij_inverse(f)){
  g1 = g2};
/***  event 10 max_exps 7479 net_exps 872 rules 51262***/

theorem bij_inverse_thm1(
			 tau:type;
			 sigma:type;
			 f:bijection(sigma,tau);
			 g =def bij_inverse(f)){
  is(g,bijection)
  }{
  show(x:sigma){inhabited(preimage(x,g))}{witness(f(x))};
  show(x:sigma;y:preimage(x,g)){y=f(x)};
  show(x:sigma){unique(preimage(x,g))}};
/***  event 11 max_exps 11215 net_exps 93 rules 183123***/

define composition(
		   sigma:type;
		   tau:type;
		   gamma:type;
		   f:tau=>gamma;
		   g:sigma=>tau){
  lambda(x:sigma){f(g(x))}};
/***  event 12 max_exps 20738 net_exps 2727 rules 49942***/

clear_event(bij_inverse_thm2);
/***  after 12 composition;***/

theorem bij_inverse_thm2 (
			  s:type;
			  u:type;
			  f:bijection(s,u)){
  composition(bij_inverse(f),f) = id_fun(s) && composition(f,bij_inverse(f)) = id_fun(u)};
/***  event 13 max_exps 13416 net_exps 3693 rules 59276***/


clear_event(bij_composition_thm);
/***  after 13 bij_inverse_thm2;***/

theorem bij_composition_thm (
			     s:type;
			     u:type;
			     v:type;
			     f:bijection(u,v);
			     g:bijection(s,u)){
  is(composition(f,g),bijection)
  }{
  show(z:v){inhabited(preimage(z,composition(f,g)))}{
    using(pre1 =def the(preimage(z,f))){
      witness(the(preimage(pre1,g)))}};
  show(z:v){unique(preimage(z,composition(f,g)))}{
    show(
	 x1:preimage(z,composition(f,g));
	 x2:preimage(z,composition(f,g))){
      x1=x2}{
      show{g(x1)=g(x2)}}}
  };
/***  event 14 max_exps 56082 net_exps 3299 rules 800183***/

define permutation(sigma:type){bijection(sigma,sigma)};
/***  event 15 max_exps 494 net_exps 494 rules 1170***/

theorem permutation_thm1 (
			  s:type;
			  f:permutation(s);
			  g:permutation(s)){
  is(composition(f,g),permutation(s))};
/***  event 16 max_exps 10218 net_exps 2552 rules 219829***/

theorem permutation_thm2(
			 s:type;
			 f:permutation(s)){
  composition(f,bij_inverse(f)) = id_fun(s)};
/***  event 17 max_exps 3417 net_exps 1406 rules 93035***/

define associative(s:type){
  assert(f:s=>s=>s){
    forall(x:s;y:s;z:s){
      f(x,f(y,z))=f(f(x,y),z)}}};
/***  event 18 max_exps 9227 net_exps 913 rules 52001***/

define perm_composition(
			s:type;
			f:permutation(s);
			g:permutation(s)){
  composition(s,s,s,f,g)};//{lambda(x:s){f(g(x))}};
/***  event 19 max_exps 12948 net_exps 269 rules 347544***/

clear_event(composition_of_perms);
/***  after 19 perm_composition;***/

theorem composition_of_perms(s:type; p1:permutation(s); p2:permutation(s)){is(perm_composition(p1,p2), permutation(s))};
/***  event 20 max_exps 13370 net_exps 830 rules 371698***/

//needed to get the arrow type for op required in the next theorem
//permutation(s)=>(permutation(s)=>permutation(s))
theorem composition_of_perms2(
			      s:type;
			      p:permutation(s);
			      f =def perm_composition(p)){
  is(f, permutation(s)=>permutation(s))};
/***  event 21 max_exps 14947 net_exps 70 rules 407874***/

clear_event(id_is_a_perm);
/***  after 21 composition_of_perms2;***/

theorem id_is_a_perm(
		     s:type){
  is(id_fun(s), permutation(s));
  }{
  show(x:s){is(idfun(s),bijection)}};
/***  {
  {
    in 22 id_is_a_perm;
    1.s:type;
    2.user_error:{
      desugar does not recognize;
      is(id_fun(s),permutation(s));};
    3.ERROR;}}***/

sugar(intern_exp(`{is(id_fun(s),permutation(s))}))
/***  {
    45;
    is(id_fun(s),permutation(s))}***/

theorem composition_assoc_perms(s:type){
  is(perm_composition(s), associative(permutation(s)))};
/***  {
  {
    in 22 composition_assoc_perms;
    1.s:type;
    2.goal(is(permutation(s),type));
    3.PROOF FAILURE;}}***/

sugar(type_of(intern_exp(`{permutation(s)})))
/***  {46;type}***/

/* using(op =def perm_composition(s)){ */
  /*     show(px:permutation(s), */
	      /* 	 py:permutation(s), */
	      /* 	 pz:permutation(s)){op(px,op(py,pz)) = op(op(px,py),pz)}}; */




