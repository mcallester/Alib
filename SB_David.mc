/** ========================================================================
Uses functions
========================================================================**/
where();

clear_event(Schroeder_Bernstein);

exp_limit[0] = 200000;

theorem Schroeder_Bernstein (
			     tau:type,
			     sigma:type,
			     inhabited(injection(sigma,tau)),
			     inhabited(injection(tau,sigma))){
  inhabited(bijection(tau,sigma))
  }{
  using(f:injection(sigma,tau),
	g:injection(tau,sigma),
	usef =mu assert(x:sigma){not(inhabited(preimage(x,g))) || exists(xx:usef){x = g(f(xx))}}, //would like to say is(x, g(some f(some usef)))
	h = lambda(x:sigma){if(is(x,usef),f(x),the(y:tau){g(y)=x})}){
    show{is(h,surjection(sigma,tau))}{
      show(y:tau){inhabited(preimage(y,h))}{
	using(is(g(y),usef)){
	  using(xx:assert(xx:usef){g(y) = g(f(xx))}){
	    classify(f(xx));}};
	using(not(is(g(y),usef))){witness(g(y))}}};
    show{is(h,injection(sigma,tau))}{
      show(y:tau){unique(preimage(y,h))}};
    witness(h)}};
