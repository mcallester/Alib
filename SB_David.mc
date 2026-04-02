
restart_event(`schroeder_bernstein_functions);

declare_package(`schroeder_bernstein_functions);

/** ========================================================================
empty set exists
========================================================================**/

package[0]

check_for_corruption[0] = 1;

proof_stepping[0] = 0;

intern_stepping[0] = 0;

current_events[0]

break_on_user_error[0] = 1;

// ========= voodoo block
clear_event(sets_exist);

// compile new code here

theorem sets_exist {inhabited(set)}{sorry};

finish();
/** there is no suspended event to finish **/

// ====== end of voodoo block ====

clear_event(emptyset_exists);
/** emptyset_exists has not been defined as an event **/

theorem emptyset_exists{exists(s:set){empty(s)}
  }{
  using(s:set){classify(assert(x:s){not(x=x)})}
  };

define preimage(s:set, w:set, y:w, h:s=>w){
  assert(x:s){h(x)=y}};

define injection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      unique(preimage(s,w,y,f))}}};

define surjection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      inhabited(preimage(s,w,y,f))}}};

define bijection(s:set,w:set){
  assert(f:s=>w){
    is(f,injection(s,w)) && is(f,surjection(s,w))}};

//three versions of bijections_invert. Identical except for the
//injection proof which is modified to exhibit the issue motivating
//congruence on quantified expressions, with the last one requiring the bvars.

theorem bijections_invert(s:set, w:set){
  inhabited(bijection(s,w)) |=> inhabited(bijection(w,s))
  }{
  using(f:bijection(s,w),
        g = lambda(x:w){the(y:s){f(y)=x}}){
    show{is(g,injection(w,s))}{
      show(y:s, x1:assert(x:w){g(x)=y}, x2:assert(x:w){g(x)=y}){x1=x2}{
        show{f(y)=x1}{classify(x1)};
        show{f(y)=x2}{classify(x2);};};
      classify(g)};
    show{is(g,surjection(w,s))}{
      show(x:s){is(f(x), preimage(w,s,x,g))};};
    show{is(g,bijection(w,s))}; 
    }};

clear_event(empty_uniqueness);
/** empty_uniqueness has not been defined as an event **/

theorem empty_uniqueness (c:class) {
  unique(assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))})}{
  using(){
    show(x1:assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))},
         x2:assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))}){
      x1=x2
      }{
      show{x1 = lambda(z:c){x1(z)}};
      show{x2 = lambda(z:c){x2(z)}};
      show(y:c){x1(y)=x2(y)}{
        show{x1(y) |=> x2(y)};
        show{x2(y) |=> x1(y)};};};}};

theorem test_injectivity (s:set, w:set, f:injection(s,w), x_2:s, x_3:s, f(x_2)=f(x_3)){
  x_2=x_3}{
  classify(f(x_2)); classify(x_3); classify(x_2)};

theorem Schroeder_Bernstein (
			     s:set,
			     w:set,
			     inhabited(injection(s,w)),
			     inhabited(injection(w,s))){
  inhabited(bijection(s,w))}{
  using(
	f:injection(s,w),
	g:injection(w,s),
	usef =mu make_set(x:s){not(exists(y:w){not(is(g(y),in(usef))) && g(y) = x})}){
    classify(lambda(x:s){if(is(x,in(usef)),f(x),the(y:w){g(y)=x})})}};

/** ========================================================================

{show(x:s){
  use_f(x) = use_f(g(f(x)))}{
  using(assert_type_from_use_f = 
	assert(yyy:preimage(w,s,g(f(x)),g)){
	  not(exists(xxx:preimage(s,w,yyy,f)){
		use_f(xxx)})}){
    
    //it would be helpful for user to indicate intention about habitation and system to complain
    //here we need refutation to see type habitation and that isn't tried in adjust_formula because we don't have a way to tell it our expectation
    using(not(inhabited(assert_type_from_use_f)),
	  suppose_not){
      classify(x); classify(f(x)); classify(g(f(x)))};
    
    //it would be helpful for user to indicate intention about habitation and system to complain
    using(suppose_not, //needed here to see next type inhabited. NOTE: no way to specify this analysis on the way out/popping
	  yy:assert_type_from_use_f){
      show{yy=f(x)}{classify(yy); classify(x); classify(f(x)) classify(g(f(x)))}; //any such yy is f(x) given injectivity of g
      }}};

using(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
  show(){is(h,injection(s,w))}{
    show(y:w,
	 x_2:preimage(s,w,y,h),
	 x_3:preimage(s,w,y,h)){
      x_2 = x_3
      }{
      show(use_f(x_2)){use_f(x_3)}{using(suppose_not){classify(x_2)}};
      show(use_f(x_3)){use_f(x_2)}{using(suppose_not){classify(x_3)}};
      using(suppose_not){classify(x_2); classify(x_3)}}};
  
  show(){is(h,surjection(s,w))}{
    show(y:w){exists(x:s){h(x)=y}}{
      using(not(inhabited(preimage(s,w,y,f)))){
	classify(y); classify(g(y));
	show{not(use_f(g(y)))}{
	  using(suppose_not)};};
      using(use_f(g(y)),
	    pre = the(preimage(s,w,y,f))){
	//this case unfinished
	show{is(y,preimage(w,s,g(y),g))};
	show(use_f(pre)){
	  using(suppose_not){
	    classify(g(y));
	    classify(y); 
	    classify(pre)}};
	classify(g(y));
	classify(pre)}}}}
  }

========================================================================**/

//WORKING PROOF OF INJECTION SUPERSEDED ABOVE
// injection works but needs exploration. Also still want to try the() and taxonomic
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  with(f:injection(s,w),
       g:injection(w,s),
       use_f =μ lambda(x:s){
         not(exists(y:preimage(w,s,x,g)){
               not(exists(z:preimage(s,w,y,f)){
                     use_f(z)})})}){
    with(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
      show(){is(h,injection(s,w))}{
        show(x:s){use_f(x) |=> f(x)=h(x)};
        show(x:s){not(use_f(x)) |=> the(y:w){g(y)=x}=h(x)};
        show(y:w){unique(preimage(s,w,y,f))};
        show(x:s){unique(preimage(w,s,x,g))};
        
        //show(x:s){is(preimage(w,s,x,g),w)}; need guidance on this
        
        show(x:s, //apply fixed point of use_f
             not(use_f(x)),
             y:preimage(w,s,x,g),
             xx:preimage(s,w,y,f)){
          not(use_f(xx))}{
          with(yy:assert(yyy:preimage(w,s,x,g)){
                 not(exists(xxx:preimage(s,w,yyy,f)){use_f(xxx)})}){
            show{yy=y}{with(focus(y), focus(yy))};}};
        
        //explore why this doesn't eliminate the body in show_case_contradictory
        //show(x:s,
               //   not(use_f(x))){
          //forall(y:preimage(w,s,x,g)){
            //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
        show(x_1:w,
             x_2:preimage(s,w,x_1,h),
             x_3:preimage(s,w,x_1,h)){
          x_2 = x_3
          }{
          show_case_contradictory(use_f(x_2) && not(use_f(x_3))){
            with(focus(x_3), focus(x_1), focus(x_2)){
              //show{forall(y:preimage(w,s,x_3,g)){
                  //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              show{forall(y:preimage(w,s,x_3,g)){
                  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              }};
          show_case_contradictory(use_f(x_3) && not(use_f(x_2))){
            with(focus(x_3), focus(x_1), focus(x_2))};
          with(assume_not_goal,focus(x_2), focus(x_3)){
            show_case(use_f(x_3))}}};
      show(){is(h,surjection(s,w))}{
        show(x1:w){exists(x2:s){h(x2)=x1}}{
          show_case(use_f(g(x1))){
            with(focus(g(x1)),
                 z:assert(x2:s){f(x2)=x1},
                 focus(z))}}}}}};


//trying ontic approach
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  
  with(f:injection(s,w),
       g:injection(w,s),
       covered_by_g =μ lambda(y:w){
         not(inhabited(preimage(s,w,y,f))) 
         || exists(yy:w){covered_by_g(yy) && y=f(g(yy))}}){
    show(x:s,covered_by_g(f(x))){ //the() safety for defining h()
      inhabited(preimage(w,s,x,g))}{
      with(focus(f(x)), //needed to avoid existence supposition for y:
           y:assert(yy:w){covered_by_g(yy) && f(x)=f(g(yy))}){
        show{is(y,preimage(w,s,x,g))}{
          show{x=g(y)}{with(focus(g(y)))};};}};
    with(uses_g = lambda(x:s){exists(y:preimage(w,s,x,g)){covered_by_g(y)}},
         h = lambda(x:s){if(uses_g(x),
                            the(preimage(w,s,x,g)),
                            f(x))}){
      show(){is(h,injection(s,w))}{
        show(y:w,
             x_2:preimage(s,w,y,h),
             x_3:preimage(s,w,y,h)){
          x_2=x_3}{
          show_case(uses_g(x_2)){
            show{unique(preimage(w,s,x_2,g))}{with(focus(x_2))};
            show{h(x_2)=the(preimage(w,s,x_2,g))};
            show{h(x_2)=y};
            show{covered_by_g(y)};
            show_case(not(uses_g(x_3))){
              
              };
            with(focus(x_2),focus(x_3))
            };
          show_case(not(uses_g(x_2)));}};}}};

//not used below here, obsolete
define inverse(s:set,w:set,f:bijection(s,w)){
  assert(g:bijection(w,s)){
    forall(x:w){f(g(x))=x} &&
    forall(y:s){g(f(y))=y}}};

theorem inverses_exist (s:set, w:set, f:bijection(s,w)){
  inhabited(inverse(s,w,f))}{
  let(g = lambda(x:w){the(y:s){f(y)=x}}){
    lemma{show(is(g,bijection(w,s)))}}
  };
