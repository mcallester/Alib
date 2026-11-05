initialize();
/***  {35;done}***/

/** ========================================================================
functions starts form initialization
========================================================================**/

declare_package(`functions);
/***  {36;done}***/

clear_event(start_functions);
/***  after 0 initialization;***/

break_on_user_error[0] = 1;
/***  {37;done}***/

define start_functions true;
/***  event 1 max_exps 0 net_exps 0 rules 0***/

where();
/***  {after 1 start_functions;}***/

exp_limit[0] = 100000;
/***  {38;done}***/

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
/***  event 8 max_exps 9481 net_exps 131 rules 101284***/

define bij_inverse(
		   tau:type;
		   sigma:type;
		   f:bijection(sigma,tau)){
  the(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}};
/***  event 9 max_exps 5928 net_exps 636 rules 20249***/

theorem bij_inverse_implementation(
				   tau:type;
				   sigma:type;
				   f:bijection(sigma,tau);
				   g1 =def lambda(y:tau){the(preimage(y,f))};
				   g2 =def bij_inverse(f)){
  g1 = g2};
/***  event 10 max_exps 7495 net_exps 872 rules 51283***/

theorem bij_inverse_thm1(
			 tau:type;
			 sigma:type;
			 f:bijection(sigma,tau);
			 g =def bij_inverse(f)){
  is(g,bijection)
  }{
  show(x:sigma){inhabited(preimage(x,g))}{witness(f(x))};
  show(x:sigma;y:preimage(x,g)){y=f(x)};};
/***  event 11 max_exps 11231 net_exps 93 rules 171737***/

define composition(
		   sigma:type;
		   tau:type;
		   gamma:type;
		   f:tau=>gamma;
		   g:sigma=>tau){
  lambda(x:sigma){f(g(x))}};
/***  event 12 max_exps 20738 net_exps 2727 rules 49942***/

theorem bij_inverse_thm2 (
			  s:type;
			  u:type;
			  f:bijection(s,u)){
  composition(bij_inverse(f),f) = id_fun(s) && composition(f,bij_inverse(f)) = id_fun(u)};
/***  event 13 max_exps 13416 net_exps 3693 rules 59282***/

theorem bij_composition_thm (
			     s:type;
			     u:type;
			     v:type;
			     f:bijection(u,s);			     
			     g:bijection(v,u);
			     h =def composition(f,g)){
  is(h,bijection)}{
  show(xs:s){inhabited(preimage(xs,h))}{
    using(xu:preimage(xs,f);xv:preimage(xu,g))}};
/***  event 14 max_exps 54559 net_exps 3941 rules 473396***/

define permutation(sigma:type){bijection(sigma,sigma)};
/***  event 15 max_exps 499 net_exps 499 rules 1182***/

theorem permutation_thm1 (
			  s:type;
			  f:permutation(s);
			  g:permutation(s)){
  is(composition(f,g),permutation(s))};
/***  event 16 max_exps 9647 net_exps 2547 rules 218666***/

theorem permutation_thm2(
			 s:type;
			 f:permutation(s)){
  composition(f,bij_inverse(f)) = id_fun(s)};
/***  event 17 max_exps 3038 net_exps 1406 rules 92169***/

define associative(s:type){
  assert(f:s=>s=>s){
    forall(x:s;y:s;z:s){
      f(x,f(y,z))=f(f(x,y),z)}}};
/***  event 18 max_exps 9355 net_exps 913 rules 58985***/

define perm_composition(
			s:type;
			f:permutation(s);
			g:permutation(s)){
  composition(s,s,s,f,g)};//{lambda(x:s){f(g(x))}};
/***  event 19 max_exps 12380 net_exps 269 rules 346142***/

theorem composition_of_perms(s:type; p1:permutation(s); p2:permutation(s)){is(perm_composition(p1,p2), permutation(s))};
/***  event 20 max_exps 12802 net_exps 830 rules 370296***/

theorem composition_of_perms2(
			      s:type;
			      p:permutation(s);
			      f =def perm_composition(p)){
  is(f, permutation(s)=>permutation(s))};
/***  event 21 max_exps 14379 net_exps 70 rules 406787***/

theorem id_is_a_perm(
		     s:type){
  is(id_fun(s), permutation(s))
  };
/***  event 22 max_exps 2845 net_exps 1721 rules 309563***/
