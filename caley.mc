
restart_event(`caley);
/** {35;done} **/

declare_package(`caley);
/** {36;done} **/

/** ========================================================================
empty set exists
========================================================================**/

check_for_corruption[0] = 1;
/** {37;done} **/

proof_stepping[0] = 0;
/** {38;done} **/

intern_stepping[0] = 0;
/** {39;done} **/

current_events[0]
/** {40;} **/

break_on_user_error[0] = 0;
/** {41;done} **/

clear_event(emptyset_exists);
/** emptyset_exists has not been defined as an event **/

theorem emptyset_exists(tau:type){exists(s:set_of(tau)){empty(in(s))}
  }{
  //show{empty(in(the_set(x:tau){not(x=x)}))};
  classify(the_set(x:tau){not(x=x)})
  };
/** {42;done} **/

theorem sets_exist (foo:type){inhabited(set_of(foo))}{};
/** {43;done} **/

/** ========================================================================
preimage
========================================================================**/

exp_limit[0]=500000;
/** {44;done} **/

clear_event(preimage);
/** preimage has not been defined as an event **/

define preimage(tau:type, sigma:type, y:sigma, h:tau=>sigma){
  assert(x:tau){h(x)=y}};
/** {45;done} **/

int_exp(max_total[0])
/** {46;2245} **/

clear_event(injection);
/** injection has not been defined as an event **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** attempt to rerun the previous successful event injection;first run clear_event(injection);note that clearing previously successful event deletes following events. ; **/

//event_max_counts()
int_exp(max_total[0])
/** {48;1826} **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** {49;done} **/

int_exp(max_total[0])
/** {50;3093} **/

clear_event(bijection)
/** bijection has not been defined as an event **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** {51;done} **/

int_exp(max_total[0])
/** {52;4059} **/

clear_event(bijections_invert);
/** bijections_invert has not been defined as an event **/

theorem bijections_invert(tau:type,sigma:type,inhabited(bijection(tau,sigma))){
  inhabited(bijection(sigma,tau))
  }{
  using(
        f:bijection(tau,sigma),
        g = lambda(x:sigma){the(y:tau){f(y)=x}}
        //intern_cps(lambd(x:sigma){...})
        ///decl(x:sigma)
        ////intern_cps(the(assert(y:tau){f(y)=x}))
        
        /////backchain(inhabited(assert(...)))
        //////analyze(inhabited(...))
        ///////classify(f) binds a surjection variable to f
        ///////yields forall(y:tau)exists(x:sigma)f(x)=y
        ///////yields exists(x:sigma)f(x)=y
        ///////yields the backchain goal.
        
        /////backchain(unique(assert(...)))
        //////analyze(unique(...))
        ///////classify(f) binds an injection variable to f.
        ///////yields forall(y:sigma){unique(assert(x:tau){f(x) = y})}
        ///////yields unique(x:sigma)f(x)=y
        ///////yields the backchain goal.
        
        
        //analyze(g)
        ///classify(f) generates the desired habitation and uniquenes formulas
        //    A.forall(x:sigma){inhabited(preimage(x,f))}
        //    B.forall(x:sigma){unique(preimage(x,f))}
        //    C.f:tau=>sigma
        //classify(g) then places g under bijection which proves the goal.
        //    1.show(forall(x:tau){inhabited(preimage(x,[g@mvar:sigma=>tau]))}
        //    2.show(forall(x:tau){unique(preimage(x,[g@mvar:sigma=>tau]))}
        //    3.show(inhabited(preimage(gvar(tau),[g@mvar:sigma=>tau]))
        //    4.show(unique(preimage(gvar(tau),[g@mvar:sigma=>tau]))
        //    5.show(inhabited(assert(y:sigma){[g@mvar:sigma=>tau](y)=gvar(tau)}))  //step1: create gvar(sigma)
        //    6.show(unique(assert(y:sigma){[g@mvar:sigma=>tau](y)=gvar(tau)}))
        //    7.show(inhabited(assert(y:sigma){the(z:tau){f(z)=y}=gvar(tau)}))


        //    9.the(z:tau){f(z)=f(gvar(tau))} = gvar(tau)    //using existential witness f(gvar(tau))

        //the(z:tau){f(z)=y}=gvar(tau)  iff  y=f(gvar(tau)) && gvar(tau):tau

        //11.the(z:rho){phi[y,z]}=c iff (phi[y,c] && c:rho)    //step2: alternative matrix for goal

        //(renamed x to y)

        //13.show(exists(y:sigma){y=f(gvar(tau))})  //step3: notice this silly kind of existential goal somehow
        //15.show(is(f(gvar(tau)),sigma))  //done  eg from f(gvar(tau)) = f(gvar(tau))
        ){	
    witness(g)
    }};
/** {53;done} **/

int_exp(max_total[0])
/** {54;11772} **/

clear_event(empty_uniqueness);
/** empty_uniqueness has not been defined as an event **/

theorem empty_uniqueness (tau:type) {
  unique(assert(s:set_of(tau)){empty(in(s))})}{
  show(x1:assert(s:set_of(tau)){empty(in(s))},
       x2:assert(s:set_of(tau)){empty(in(s))}){
    x1=x2}};
/** {55;done} **/

clear_event(test_injectivity);
/** {56;done} **/

theorem test_injectivity (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ //x_3:preimage(f,f(x_2))
  x_2=x_3}{
  classify(f)
  };
/** {
    in event test_injectivity;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_decl(f:injection(tau,sigma));
    4.show_decl(x_2:tau);
    5.show_decl(x_3:tau);
    6.show_assume(equal(f(x_2),f(x_3)));
    7.push_goal(equal(x_2,x_3));
    completed classifying f;
    8.backchaining(equal(x_2,x_3));
    completed analyzing x_2;
    completed analyzing x_3;
    Failure to show equal(x_2,x_3)} **/

step();
/** there is no suspended event to step **/

define permutation(s:type){
  assert(f:s=>s){is(f,injection(s,s)) && is(f,surjection(s,s))}
  };
/** {57;done} **/

break_on_user_error[0] = 1;
/** {58;done} **/

clear_event(group)
/** group has not been defined as an event **/

class group () {
  member:type,
  op:member=>member=>member,
  associative(member,op),
  id:member,
  forall(x:member){op(id,x) = x && op(x,id) = x},
  inv:member=>member,
  forall(x:member){op(x,inv(x)) = id && op(inv(x){
    {};
    {
      desugar does not recognize;
      member:type}},x) = id}
  };
/**  **/

define composition(s:set,u:set,w:set,f:s=>u,g:u=>w){
  lambda(x:s){g(f(x))}
  };

class naked_set(){member:set};

define the_subtype(s:set,P:s=>bool){
  obj(naked_set,member=assert(x:s){P(x)})
  };

define caley_bijection(G:group,x:G.member){
  lambda(y:G.member){G.op(x,y)}
  };


define caley_set(G:group){
  the_subtype(permutation(G.member),
	      lambda(f:permutation(G.member)){
		exists(x:G.member){f = caley_bijection(G,x)}})
  };

define caley_group(G:group){
  obj(group,
      member = caley_set(G).member,
      op = lambda(f:member,g:member){composition(G.member,G.member,G.member,f,g)},
      inv = lambda(f:member){inverse(member,f)},
      id = lambda(f:member){f})
  };

theorem(G:group){
  lemma{is(caley_bijection(G),
	   isomorphism(G,caley_group(G)))}
  isomorphic(G,caley_goup(G))
  }


