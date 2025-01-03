restart_event(`initialize_alfred);

define{
  injection(s:set,w:set){
    assert(f:s*->w){
      forall(y:w){
	unique(assert(x:s){y = f(x)})}
      }}};

define{
  surjection(s:set,w:set){
    assert(f:s*->w){
      forall(y:w){
	exists(x:s){
	  f(x)=y}}}}};

define{
  bijection(s:set,w:set){
    assert(f:s*->w){
      is(f,injection(s,w)) && is(f,surjection(s,w))}}};

theorem{SB;
  (s:set,
   w:set,
   suppose(inhabited(injection(s,w))),
   suppose(inhabited(injection(w,s))))
  {
    inhabited(bijection(s,w))
    }{
    let(f:injection(s,w),
	g:injection(w,s),
	usef =μ assert(x:s){
	  not(exists(y:w){
		g(y)=x
		&& not(exists(z:s){
			 f(z)=y && z:usef})})},
	h = lambda(x:s){
	  if(x:usef,f(x),the(y:w){g(y)=x})}){
      show(h:bijection(s,w))}}};
