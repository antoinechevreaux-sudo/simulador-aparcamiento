/* ===== Ángulo de Maniobra en el simulador (teléfono virtual) ===== */
/* Ángulo de Maniobra · cerebro común (el mismo código en el teléfono y en el simulador).
   Sin DOM: recibe los datos de los sensores con su hora (ms) y avisa con callbacks. */
(function(root){
'use strict';
const DEF={
  kmhDrive:12,   // por encima de esto durante driveMs = circulando (silencio)
  driveMs:3000,
  stopMs:2000,   // parado este tiempo = listo para aparcar (ángulo a 0)
  stopKmh:2,     // por debajo = parado (GPS)
  parkKmh:2.5,   // (lógica clásica) por encima, tras parar = maniobra
  parkDeg:3,     // (lógica clásica) giro que inicia la maniobra
  quietAcc:0.25, // (lógica clásica) sin GPS: vibración por debajo = parado (m/s²)
  gpsMs:5000,    // sin datos de GPS en este tiempo = sin GPS
  hyst:3,        // grados que hay que bajar para volver a armar un aviso
  lv1:25, lv2:45,
  soloAtras:1,   // 1 = lógica nueva: solo avisa si el coche arranca marcha atrás
  restAcc:0.13,  // umbral mínimo de vibración (m/s²) para «quieto con el motor en marcha»
  restK:2.4,     // el umbral se adapta: veces la vibración más baja medida (ralentí)
  restMs:300,    // tiempo quieto para considerarlo parado de verdad
  revV:0.2,      // m/s estimados para decidir hacia dónde arranca
  fwdExitMs:6000 // en maniobra: avanzar sin parar este tiempo = se acabó la maniobra
};
function create(opts){
  const P=Object.assign({},DEF,opts||{});
  const cb={alert(){},mode(){},log(){}};
  let source=null,axis=null,refYaw=null,lastYaw=null,unwrapped=0,angle=0;
  let gx=0,gy=0,gz=9.8,lastGT=0,gyroAngle=0,startT=0;
  let lastDop=-1e12,spd2=0,fixes=[],derived=false,mode='always',speed=null,lastFix=-1e12,prevFix=null,stopSince=0,fastSince=0,accVar=0,lastAccT=-1e12;
  let floor=0.059,thr=0.13,R=null,accFast=0,quietMs=0,atRest=false,restYaw=null,restT=0,vEst=0,bias=0,lastMT=null,fromRest=false;
  let lastDir=0,zRest=0,evt=null,fwdSince=0,fsign=1,corr=0,accSum=0,accN=0,prevSpd=null,vibRest=0,vibMove=0;
  const armed={1:true,2:true};
  const log=(t,m)=>cb.log(t,m);
  const gpsOk=t=>t-lastFix<P.gpsMs&&speed!=null;

  function setMode(m,t,why){ if(mode===m)return; const o=mode; mode=m; if(m==='park'){armed[1]=armed[2]=true;fwdSince=0;fastSince=0}
    log(t,o+' → '+m+(why?' ('+why+')':'')); cb.mode(m,t,o) }
  function checkAlerts(t){
    if(mode!=='park'&&mode!=='always')return;
    if(mode==='park'&&P.soloAtras&&lastDir>0)return; // en la maniobra, solo pita yendo marcha atrás
    const v=Math.abs(angle);
    [[1,P.lv1],[2,P.lv2]].forEach(([k,l])=>{ if(armed[k]&&v>=l){armed[k]=false;log(t,'PITIDO '+l+'° (ángulo '+v.toFixed(1)+'°)');cb.alert(l,t,angle)} else if(!armed[k]&&v<l-P.hyst)armed[k]=true });
  }
  function setAngle(a,t){angle=a;checkAlerts(t)}
  function zero(t,why){axis=null;lastYaw=null;refYaw=null;unwrapped=0;gyroAngle=0;angle=0;restYaw=null;armed[1]=armed[2]=true;log(t,'ángulo a 0°'+(why?' ('+why+')':''))}
  // pone el 0 en el rumbo que tenía el coche mientras estaba parado (aunque ya haya empezado a moverse)
  function zeroAtRest(t){ if(restYaw!=null&&source==='orient'){refYaw=restYaw;armed[1]=armed[2]=true;angle=-(unwrapped-refYaw);log(t,'ángulo a 0° (rumbo de la parada)')} else zero(t,'parado') }

  function yawFromEuler(a,b,g){
    const d=Math.PI/180,cA=Math.cos(a*d),sA=Math.sin(a*d),cB=Math.cos(b*d),sB=Math.sin(b*d),cG=Math.cos(g*d),sG=Math.sin(g*d);
    R=[[cA*cG-sA*sB*sG,-cB*sA,cA*sG+cG*sA*sB],[cG*sA+cA*sB*sG,cA*cB,sA*sG-cA*cG*sB],[-cB*sG,sB,cB*cG]];
    const Y=[R[0][1],R[1][1],R[2][1]],Z=[R[0][2],R[1][2],R[2][2]];
    if(!axis)axis=Math.abs(Y[2])<Math.abs(Z[2])?'Y':'Z';
    const v=axis==='Y'?Y:Z;
    if(Math.hypot(v[0],v[1])<0.2)return null;
    return Math.atan2(v[1],v[0])/d;
  }
  function orient(a,b,g,t){
    if(a==null)return;
    const y=yawFromEuler(a,b||0,g||0); if(y==null)return;
    if(source!=='orient'){ if(source==='gyro')return; source='orient' }
    if(lastYaw!=null){let d=y-lastYaw;if(d>180)d-=360;if(d<-180)d+=360;unwrapped+=d}
    lastYaw=y; if(refYaw==null)refYaw=unwrapped;
    if(atRest)restYaw=unwrapped;
    setAngle(-(unwrapped-refYaw),t);
  }
  // eje delante/detrás en horizontal: pantalla hacia el conductor → −Z ; teléfono tumbado → +Y
  function fwd(){ if(!R)return null;
    const Z=[R[0][2],R[1][2],R[2][2]],Y=[R[0][1],R[1][1],R[2][1]];
    const v=Math.abs(Z[2])<0.7?[-Z[0],-Z[1]]:[Y[0],Y[1]],n=Math.hypot(v[0],v[1]);return n<0.2?null:[v[0]/n,v[1]/n] }
  function motion(e,t){
    const a=e.acceleration;let m,lin=null;
    if(a&&a.x!=null){m=Math.hypot(a.x,a.y,a.z);lin=a}
    else{const g=e.accelerationIncludingGravity;if(!g||g.x==null)return;m=Math.abs(Math.hypot(g.x,g.y,g.z)-9.81)}
    accVar+=(m*m-accVar)*0.05;lastAccT=t;
    const dt=lastMT==null?0:Math.min((t-lastMT)/1000,0.1);lastMT=t;
    if(dt>0){
      accFast+=(m*m-accFast)*Math.min(1,dt*15);
      const rms=Math.sqrt(accFast),gpsMoving=t-lastFix<1500&&!derived&&speed>4&&spd2>4; // dos lecturas seguidas en marcha
      const gpsStill=gpsOk(t)&&!derived&&speed<1;
      floor=rms<floor?floor+(rms-floor)*0.05:floor*(1+(gpsStill?0.15:0.005)*dt); // sube rápido solo si el GPS confirma que está parado
      thr=Math.min(0.6,Math.max(P.restAcc,floor*P.restK));
      if(rms<thr&&!gpsMoving)quietMs+=dt*1000;else quietMs=0;
      const wasRest=atRest;atRest=quietMs>=P.restMs;
      if(atRest){vibRest+=(rms-vibRest)*0.01; if(!wasRest){restT=t;log(t,'quieto (vibración '+rms.toFixed(2)+')')}}
      else if(gpsMoving)vibMove+=(rms-vibMove)*0.01;
      const f=fwd();
      if(lin&&f&&R){
        const wx=R[0][0]*lin.x+R[0][1]*lin.y+R[0][2]*lin.z,wy=R[1][0]*lin.x+R[1][1]*lin.y+R[1][2]*lin.z;
        const af=(wx*f[0]+wy*f[1])*fsign;accSum+=af;accN++;
        if(atRest){bias+=(af-bias)*0.05;vEst=0;fromRest=true}
        else{vEst=(vEst+(af-bias)*dt)*Math.exp(-dt/3);
          if(fromRest&&Math.abs(vEst)>P.revV){fromRest=false;evt={dir:vEst>0?1:-1,t};lastDir=evt.dir;log(t,'arranca '+(evt.dir>0?'hacia delante':'marcha atrás'))}}
      }
    }
    // giroscopio de reserva si no llega la orientación
    const r=e.rotationRate,ag=e.accelerationIncludingGravity;
    if(!r||r.alpha==null||source==='orient')return;
    if(!source){if(t-startT<700)return;source='gyro'}
    const gdt=lastGT?Math.min((t-lastGT)/1000,0.1):0;lastGT=t;
    if(ag&&ag.x!=null){gx+=(ag.x-gx)*.08;gy+=(ag.y-gy)*.08;gz+=(ag.z-gz)*.08}
    const n=Math.hypot(gx,gy,gz)||1;let w=(r.beta*gx+r.gamma*gy+r.alpha*gz)/n;
    if(Math.abs(w)<0.4)w=0;gyroAngle-=w*gdt;setAngle(gyroAngle,t);
  }
  function distM(a,b){const R=6371000,d=Math.PI/180,dl=(b.latitude-a.latitude)*d,dn=(b.longitude-a.longitude)*d;
    const h=Math.sin(dl/2)**2+Math.cos(a.latitude*d)*Math.cos(b.latitude*d)*Math.sin(dn/2)**2;return 2*R*Math.asin(Math.sqrt(h))}
  function fix(p,t){
    let s=p.coords.speed;derived=false;if(s!=null&&!isNaN(s))lastDop=t;
    // sin velocidad del GPS: se calcula con posiciones separadas al menos 4 s (con menos, el error de posición la dispara)
    fixes.push(p);while(fixes.length>2&&p.timestamp-fixes[1].timestamp>=4000)fixes.shift();
    if((s==null||isNaN(s))&&!P.soloAtras&&prevFix){const d=distM(prevFix.coords,p.coords),dt=(p.timestamp-prevFix.timestamp)/1000;if(dt>0)s=d/dt}
    else if((s==null||isNaN(s))&&t-lastDop<10000){accSum=0;accN=0;return} // hay velocidad del GPS normalmente: se ignora esta lectura
    else if(s==null||isNaN(s)){const q=fixes[0],dt=(p.timestamp-q.timestamp)/1000;s=dt>=4?distM(q.coords,p.coords)/dt:null;derived=true}
    prevFix=p;lastFix=t;
    if(s!=null&&!isNaN(s)){
      // comprueba con el GPS que el eje delante/detrás no está al revés
      if(prevSpd!=null&&accN>10&&(mode==='drive'||mode==='creep')){const ga=s-prevSpd,am=accSum/accN;if(Math.abs(ga)>0.5&&Math.abs(am)>0.2)corr=corr*0.9+Math.sign(ga)*Math.sign(am);
        if(corr<-3){fsign=-fsign;corr=0;log(t,'eje delante/detrás corregido')}}
      prevSpd=s;spd2=derived?0:(speed||0);speed=s*3.6}
    else speed=null;
    accSum=0;accN=0;
  }
  function gpsDenied(t){ if(!P.soloAtras){mode='always';log(t,'sin permiso de ubicación: siempre activo');cb.mode('always',t)} }
  function start(t,hasGeo){startT=t;mode=hasGeo||P.soloAtras?'stop':'always';log(t,'inicio · modo '+mode)}

  function tickClassic(t){
    const ok=gpsOk(t),quiet=Math.sqrt(accVar)<P.quietAcc,stopped=ok?speed<P.stopKmh:quiet;
    stopSince=stopped?(stopSince||t):0;
    fastSince=(ok&&speed>P.kmhDrive)?(fastSince||t):0;
    if(mode==='drive'&&stopSince&&t-stopSince>P.stopMs){setMode('stop',t,'parado');zero(t,'parado')}
    else if(mode==='stop'&&(Math.abs(angle)>P.parkDeg||(ok&&speed>P.parkKmh)))setMode('park',t,'movimiento');
    if(fastSince&&t-fastSince>P.driveMs)setMode('drive',t,'circulando');
  }
  function tick(t){
    if(mode==='always')return;
    const hasAcc=t-lastAccT<2000&&R;
    if(!P.soloAtras||!hasAcc)return tickClassic(t);
    const fresh=t-lastFix<2000&&speed!=null;
    fastSince=(fresh&&speed>P.kmhDrive)?(fastSince||t):0;
    stopSince=atRest?restT:0;
    if((mode==='drive'||mode==='creep')&&stopSince&&t-stopSince>=P.stopMs){setMode('stop',t,'parado');zeroAtRest(t);zRest=restT;
      if(evt&&evt.t<restT)evt=null}
    if(mode==='stop'&&atRest&&restT!==zRest){zRest=restT;zeroAtRest(t)}
    if(mode==='stop'&&evt&&evt.t>=restT-50){
      if(evt.dir<0)setMode('park',t,'marcha atrás');else setMode('creep',t,'hacia delante');evt=null}
    // si arranca marcha atrás antes de cumplirse stopMs, la parada vale igual
    if((mode==='drive'||mode==='creep')&&evt&&evt.dir<0&&restT&&evt.t>restT){
      setMode('stop',t,'parada corta');zeroAtRest(t);zRest=restT;setMode('park',t,'marcha atrás');evt=null}
    if(mode==='park'){ if(atRest)fwdSince=0; else if(evt&&evt.dir>0&&!fwdSince)fwdSince=evt.t;
      if(fwdSince&&t-fwdSince>P.fwdExitMs){setMode('creep',t,'sale hacia delante');fwdSince=0}
      if(evt&&evt.dir<0)fwdSince=0; }
    if(fastSince&&t-fastSince>P.driveMs)setMode('drive',t,'circulando');
  }
  return {P,cb,orient,motion,fix,tick,start,gpsDenied,
    zero(t){zero(t,'manual');if(mode==='drive'||mode==='creep'||mode==='stop')setMode('park',t,'manual')},
    get angle(){return angle},get mode(){return mode},get source(){return source},get atRest(){return atRest},
    get vib(){return {rest:vibRest,move:vibMove,now:Math.sqrt(accFast),thr,floor}},
    kmh(t){return gpsOk(t)?speed:null}};
}
root.AnguloCore={create,DEF};
if(typeof module!=='undefined')module.exports=root.AnguloCore;
})(typeof window!=='undefined'?window:globalThis);

/* Teléfono virtual: convierte el movimiento del coche simulado en lo que daría un teléfono real
   (orientación como Chrome Android, acelerómetro con vibración, GPS a 1 Hz con retraso y ruido). */
(function(root){
'use strict';
const DEFV={
  mount:'vertical', // vertical | horizontal (apaisado en el soporte) | plano (tumbado)
  tilt:15,          // grados que se recuesta en el soporte
  mountYaw:8,       // grados que mira hacia el conductor
  gyroNoise:0.15,   // ruido de orientación (°)
  drift:1.0,        // deriva del giroscopio (°/min)
  vib:1,            // vibración del soporte: 0.5 baja · 1 media · 2 alta
  gps:'bueno',      // bueno | ciudad | sin
  gpsLat:900,       // retraso del GPS (ms)
  gpsNoise:0.3,     // ruido de velocidad (m/s)
  seed:1
};
function rng(seed){let s=seed>>>0||1;return()=>{s^=s<<13;s>>>=0;s^=s>>17;s^=s<<5;s>>>=0;return s/4294967296}}
function create(opts){
  const O=Object.assign({},DEFV,opts||{});
  const rnd=rng(O.seed*7919+13),gauss=()=>{let u=0,v=0;while(!u)u=rnd();v=rnd();return Math.sqrt(-2*Math.log(u))*Math.cos(2*Math.PI*v)};
  const d2r=Math.PI/180;
  const add=(a,b,k)=>[a[0]+b[0]*k,a[1]+b[1]*k,a[2]+b[2]*k], sc=(a,k)=>[a[0]*k,a[1]*k,a[2]*k];
  const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];
  function rot(v,k,ang){const c=Math.cos(ang),s=Math.sin(ang);return add(add(sc(v,c),cross(k,v),s),k,dot(k,v)*(1-c))}
  // ejes del teléfono expresados en el coche (f delante, l izquierda, u arriba)
  function mountAxes(){
    const t=O.tilt*d2r,c=Math.cos(t),s=Math.sin(t),f=[1,0,0],l=[0,1,0],u=[0,0,1];
    let X,Y,Z;
    if(O.mount==='plano'){X=sc(l,-1);Y=f;Z=u}
    else if(O.mount==='horizontal'){X=add(sc(u,c),f,s);Y=l;Z=add(sc(f,-c),u,s)}
    else{X=sc(l,-1);Y=add(sc(u,c),f,s);Z=add(sc(f,-c),u,s)}
    const my=O.mountYaw*d2r;return [rot(X,u,my),rot(Y,u,my),rot(Z,u,my)];
  }
  let M=mountAxes(),hist=[],lastT=null,prevV=0,prevPsi=null,aLong=0,yawRate=0,nextFix=0,vibP=0,vibR=0,noiseA=0;
  // ángulos de Euler como los calcula Chromium a partir de la matriz
  function euler(r){let a,b,g;
    if(r[2][2]>0){a=Math.atan2(-r[0][1],r[1][1]);b=Math.asin(r[2][1]);g=Math.atan2(-r[2][0],r[2][2])}
    else if(r[2][2]<0){a=Math.atan2(r[0][1],-r[1][1]);b=-Math.asin(r[2][1]);b+=b>=0?-Math.PI:Math.PI;g=Math.atan2(r[2][0],-r[2][2])}
    else{a=Math.atan2(r[1][0],r[0][0]);b=r[2][1]>0?Math.PI/2:-Math.PI/2;g=0}
    if(a<0)a+=2*Math.PI;return[a/d2r,b/d2r,g/d2r]}
  /* s: {t ms, psi rumbo ENU en rad (izq. positivo), v m/s con signo, x,y metros} ; out: {orient,motion,fix} */
  function step(s,out){
    const dt=lastT==null?0:(s.t-lastT)/1000;lastT=s.t;
    if(dt>0){let dp=s.psi-prevPsi;while(dp>Math.PI)dp-=2*Math.PI;while(dp<-Math.PI)dp+=2*Math.PI;
      yawRate+=(dp/dt-yawRate)*Math.min(1,dt*20);aLong+=((s.v-prevV)/dt-aLong)*Math.min(1,dt*15)}
    prevV=s.v;prevPsi=s.psi;
    hist.push({t:s.t,v:s.v,x:s.x,y:s.y});while(hist.length>2&&hist[1].t<s.t-O.gpsLat-1500)hist.shift();
    // vibración: ralentí + carretera (crece con la velocidad)
    const sp=Math.abs(s.v),vibA=(0.04+0.16*Math.min(sp/3,1))*O.vib;
    vibP+=(gauss()*0.15*O.vib*Math.min(sp/2+0.2,1)-vibP)*0.2; vibR+=(gauss()*0.15*O.vib*Math.min(sp/2+0.2,1)-vibR)*0.2;
    // balanceo del soporte al acelerar/frenar
    const pitch=(vibP-aLong*0.6)*d2r,roll=(vibR+yawRate*sp*0.3)*d2r;
    const ps=s.psi,f=[Math.cos(ps),Math.sin(ps),0],l=[-Math.sin(ps),Math.cos(ps),0],u=[0,0,1];
    const toW=v=>add(add(sc(f,v[0]),l,v[1]),u,v[2]);
    let ax=M.map(toW).map(v=>rot(rot(v,l,pitch),f,roll));
    // error del giroscopio: deriva lenta + ruido, alrededor de la vertical
    const err=(O.drift/60*s.t/1000+gauss()*O.gyroNoise)*d2r; ax=ax.map(v=>rot(v,u,err));
    const Rm=[[ax[0][0],ax[1][0],ax[2][0]],[ax[0][1],ax[1][1],ax[2][1]],[ax[0][2],ax[1][2],ax[2][2]]];
    const [a,b,g]=euler(Rm); out.orient&&out.orient(a,b,g,s.t);
    // acelerómetro (sin gravedad) en ejes del teléfono
    const aw=[f[0]*aLong+l[0]*s.v*yawRate+gauss()*vibA,f[1]*aLong+l[1]*s.v*yawRate+gauss()*vibA,gauss()*vibA*1.3];
    const dev=w=>({x:dot(ax[0],w),y:dot(ax[1],w),z:dot(ax[2],w)});
    const lin=dev(aw),inc=dev([aw[0],aw[1],aw[2]+9.81]);
    const wr=dev([0,0,yawRate/d2r]);
    out.motion&&out.motion({acceleration:lin,accelerationIncludingGravity:inc,rotationRate:{alpha:wr.z,beta:wr.x,gamma:wr.y}},s.t);
    // GPS
    if(O.gps!=='sin'&&s.t>=nextFix){nextFix=s.t+1000+(O.gps==='ciudad'?gauss()*150:0);
      if(!(O.gps==='ciudad'&&rnd()<0.12)){
        const tt=s.t-O.gpsLat;let h=hist[0];for(const q of hist){if(q.t<=tt)h=q;else break}
        const tv=Math.abs(h.v);let spd=tv<0.2?Math.abs(gauss()*0.15):Math.max(0,tv+gauss()*O.gpsNoise*(O.gps==='ciudad'?2:1));
        if(O.gps==='ciudad'&&rnd()<0.15)spd=null;
        const j=O.gps==='ciudad'?6:2.5,lat=50.88+(h.y+gauss()*j)/111320,lon=4.70+(h.x+gauss()*j)/(111320*Math.cos(50.88*d2r));
        out.fix&&out.fix({coords:{speed:spd,latitude:lat,longitude:lon},timestamp:s.t},s.t);
      }
    }
  }
  return {O,step,reset(){M=mountAxes()},set(k,v){O[k]=v;if(k==='mount'||k==='tilt'||k==='mountYaw')M=mountAxes()}};
}
root.VirtualPhone={create,DEFV};
if(typeof module!=='undefined')module.exports=root.VirtualPhone;
})(typeof window!=='undefined'?window:globalThis);

/* Árbitro: sabe lo que hace el coche de verdad y comprueba si la app pitó cuando tocaba.
   Maniobra real = el coche se para y arranca marcha atrás. Referencia = rumbo en esa parada.
   Termina al circular hacia delante más de 15 m seguidos o a más de 15 km/h. */
(function(root){
'use strict';
function create(o){
  const L=Object.assign({lv1:25,lv2:45,hyst:3,tol:1500},o||{});
  let lastDir=0,lastT=null,inMan=false,stopPsi=null,ref=0,fwdDist=0,stoppedT=0,psi0=null,arm={1:true,2:true},truth=0;
  const exp=[],got=[],events=[];
  const wrap=a=>{while(a>Math.PI)a-=2*Math.PI;while(a<-Math.PI)a+=2*Math.PI;return a};
  function step(s){ // {t,psi,v}
    if(Math.abs(s.v)>0.1)lastDir=Math.sign(s.v);const sp=Math.abs(s.v),dt=lastT==null?0:(s.t-lastT)/1000;lastT=s.t;
    if(sp<0.1)stopPsi=s.psi;
    if(!inMan&&s.v<-0.1&&stopPsi!=null){inMan=true;ref=stopPsi;fwdDist=0;arm={1:true,2:true};events.push({t:s.t,k:'inicio maniobra'})}
    if(sp>0.1&&s.v>0)stopPsi=null;
    if(inMan){
      if(s.v>0)fwdDist+=s.v*dt;else if(s.v<0)fwdDist=0;
      if(fwdDist>15||sp>15/3.6){inMan=false;events.push({t:s.t,k:'fin maniobra'})}
    }
    truth=inMan?-wrap(s.psi-ref)*180/Math.PI:null;
    if(inMan){const v=Math.abs(truth),rev=lastDir<0;[[1,L.lv1],[2,L.lv2]].forEach(([k,l])=>{if(arm[k]&&v>=l&&rev){arm[k]=false;exp.push({t:s.t,l})}else if(!arm[k]&&v<l-L.hyst)arm[k]=true})}
  }
  function beep(l,t,appAng){got.push({t,l,appAng,truth})}
  function score(){
    const used=new Set();let hit=0,late=0,errSum=0;const miss=[],fals=[];
    for(const e of exp){let best=-1,bd=1e9;got.forEach((g,i)=>{if(!used.has(i)&&g.l===e.l&&Math.abs(g.t-e.t)<=L.tol&&Math.abs(g.t-e.t)<bd){bd=Math.abs(g.t-e.t);best=i}});
      if(best>=0){used.add(best);hit++;late+=got[best].t-e.t;errSum+=Math.abs(Math.abs(got[best].truth??e.l)-e.l)}else miss.push(e)}
    got.forEach((g,i)=>{if(!used.has(i))fals.push(g)});
    return {esperados:exp.length,acertados:hit,perdidos:miss.length,falsos:fals.length,retrasoMedio:hit?late/hit:0,miss,fals};
  }
  return {step,beep,score,get truth(){return truth},get inMan(){return inMan},events};
}
root.AnguloJudge={create};
if(typeof module!=='undefined')module.exports=root.AnguloJudge;
})(typeof window!=='undefined'?window:globalThis);

/* Teléfono virtual dentro del simulador: Ángulo de Maniobra funcionando con sensores simulados. */
(function(){
'use strict';
const $=id=>document.getElementById(id);
const KEY='angSimCfg';
let saved={};try{saved=JSON.parse(localStorage.getItem(KEY)||'{}')}catch(e){}
const CFGV=Object.assign({},VirtualPhone.DEFV,saved.phone||{});
const CFGA=Object.assign({},AnguloCore.DEF,saved.app||{});
const save=()=>{try{localStorage.setItem(KEY,JSON.stringify({phone:CFGV,app:CFGA,open:UI.open,big:UI.big}))}catch(e){}};
const UI={open:!!saved.open,big:!!saved.big};

/* ---------- estilos y maquetación ---------- */
const css=document.createElement('style');css.textContent=`
#vph{position:fixed;left:10px;top:calc(env(safe-area-inset-top,0px) + 92px);width:118px;z-index:7;background:#0e141c;border:3px solid #2a2f36;border-radius:16px;
 box-shadow:0 6px 18px rgba(0,0,0,.45);color:#eef1f4;font-family:"Barlow Condensed","Arial Narrow",system-ui,sans-serif;overflow:hidden;user-select:none;-webkit-user-select:none;touch-action:manipulation}
#vph.big{width:170px}
#vph[hidden]{display:none}
#vph canvas{display:block;width:100%;height:92px}
#vph.big canvas{height:140px}
#vph .vst{font:600 10px system-ui,sans-serif;letter-spacing:.03em;text-transform:uppercase;text-align:center;padding:3px 4px;color:#8a99a8;background:#151d27;border-bottom:1px solid #2a3644;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#vph .vst.park{color:#5fc7b8} #vph .vst.stop{color:#f2b33d}
#vph .vdeg{text-align:center;font-weight:700;font-size:38px;line-height:.95;font-variant-numeric:tabular-nums;color:#5fc7b8}
#vph.big .vdeg{font-size:54px}
#vph .vdeg small{font-size:.5em;color:#8a99a8}
#vph .vbar{position:relative;height:8px;margin:3px 8px 4px;background:#151d27;border:1px solid #2a3644;border-radius:3px;overflow:hidden}
#vph .vfill{position:absolute;top:0;bottom:0;left:50%;width:0;background:#5fc7b8}
#vph .vtk{position:absolute;top:0;bottom:0;width:1px}
#vph .vtruth{font:11px system-ui,sans-serif;color:#8a99a8;text-align:center;padding:0 4px 3px;font-variant-numeric:tabular-nums}
#vph .vscore{display:flex;justify-content:center;gap:8px;font:600 11px system-ui,sans-serif;padding:2px 0 4px}
#vph .vscore b{font-weight:700}
#vph .vbtn{display:flex;border-top:1px solid #2a3644}
#vph .vbtn button{flex:1;font:600 12px system-ui,sans-serif;color:#eef1f4;background:#1b2430;border:0;padding:8px 0;cursor:pointer}
#vph .vbtn button+button{border-left:1px solid #2a3644}
#vph .vbtn button:active{background:#2a3644}
#vph.flash{animation:vphf .5s}
@keyframes vphf{0%{box-shadow:0 0 0 4px #f2b33d}100%{box-shadow:0 6px 18px rgba(0,0,0,.45)}}
#vph.flash2{animation:vphf2 .6s}
@keyframes vphf2{0%{box-shadow:0 0 0 5px #f0645a}100%{box-shadow:0 6px 18px rgba(0,0,0,.45)}}
#vpp{position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);z-index:40;width:min(360px,94vw);max-height:88vh;overflow-y:auto;overscroll-behavior:contain;
 background:rgba(14,18,24,.96);color:#f1f4f8;border:1px solid rgba(255,255,255,.14);border-radius:14px;padding:12px 14px;font:13px system-ui,sans-serif;box-shadow:0 10px 30px rgba(0,0,0,.5)}
#vpp[hidden]{display:none}
#vpp h3{margin:12px 0 6px;font-size:13px;color:#a7b3c2;font-weight:600;text-transform:uppercase;letter-spacing:.05em}
#vpp h3:first-of-type{margin-top:2px}
#vpp .row{display:grid;grid-template-columns:1fr auto;gap:2px 10px;align-items:center;margin:7px 0}
#vpp .row span{color:#d5dce4}
#vpp .row em{font-style:normal;color:#8a99a8;font-size:11px;grid-column:1/-1}
#vpp .row b{font-variant-numeric:tabular-nums;min-width:52px;text-align:right}
#vpp input[type=range]{grid-column:1/-1;width:100%}
#vpp .seg{display:flex;gap:4px;grid-column:1/-1}
#vpp .seg button{flex:1;padding:7px 0;border-radius:8px;border:1px solid rgba(255,255,255,.16);background:rgba(255,255,255,.06);color:#f1f4f8;font:600 12px system-ui,sans-serif}
#vpp .seg button.on{background:#2f8bff;border-color:#2f8bff}
#vpp .acts{display:flex;flex-wrap:wrap;gap:6px;margin-top:10px}
#vpp .acts button{flex:1 1 45%;padding:9px 6px;border-radius:9px;border:1px solid rgba(255,255,255,.16);background:rgba(255,255,255,.08);color:#f1f4f8;font:600 12px system-ui,sans-serif}
#vpp .acts button.pri{background:#2f8bff;border-color:#2f8bff}
#vpp .log{font:11px ui-monospace,Menlo,Consolas,monospace;background:#0a0f15;border:1px solid #232c37;border-radius:8px;padding:6px;max-height:170px;overflow-y:auto;white-space:pre-wrap;color:#b9c4cf}
#vpp .log .b{color:#f2b33d} #vpp .log .ok{color:#5fc7b8} #vpp .log .bad{color:#f0645a}
#vpp .close{position:sticky;top:0;float:right;background:none;border:0;color:#a7b3c2;font-size:22px;line-height:1;padding:0 2px;cursor:pointer}
#vpp .note{color:#8a99a8;font-size:11px;line-height:1.4;margin:4px 0 0}
#vphb svg{display:block}
#vphb.on{background:rgba(74,163,255,.38)!important;border-color:rgba(74,163,255,.7)!important}
`;document.head.appendChild(css);

const ph=document.createElement('div');ph.id='vph';ph.hidden=!UI.open;if(UI.big)ph.classList.add('big');
ph.innerHTML=`<div class="vst" id="vpst">Listo</div><canvas id="vpcv"></canvas><div class="vdeg" id="vpdeg">0<small>°</small></div>
<div class="vbar"><div class="vfill" id="vpfill"></div><div class="vtk" style="left:22.2%;background:#f2b33d"></div><div class="vtk" style="left:77.8%;background:#f2b33d"></div><div class="vtk" style="left:50%;background:#8a99a8"></div></div>
<div class="vtruth" id="vptr">Real: –</div><div class="vscore"><span style="color:#5fc7b8">✓ <b id="vpok">0</b></span><span style="color:#f0645a">✗ <b id="vpbad">0</b></span><span style="color:#f2b33d">⌀ <b id="vpmiss">0</b></span></div>
<div class="vbtn"><button id="vp0" type="button">0°</button><button id="vpset" type="button" aria-label="Ajustes">⚙</button><button id="vpsz" type="button" aria-label="Tamaño">⤢</button></div>`;
document.body.appendChild(ph);

const pan=document.createElement('div');pan.id='vpp';pan.hidden=true;document.body.appendChild(pan);

// botón en la barra de iconos
const ico=$('ico');const btn=document.createElement('button');btn.id='vphb';btn.setAttribute('aria-label','Teléfono: Ángulo de Maniobra');btn.title='Teléfono: Ángulo de Maniobra';
btn.innerHTML='<svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="#fff" stroke-width="1.8" stroke-linejoin="round"><rect x="7" y="2.5" width="10" height="19" rx="2.2"/><path d="M12 8.5v4l2.5 1.5" stroke-linecap="round"/></svg>';
if(ico)ico.prepend(btn);else{btn.style.cssText='position:fixed;left:10px;top:60px;z-index:7';document.body.appendChild(btn)}
btn.classList.toggle('on',UI.open);

/* ---------- sonido ---------- */
let audio=null;
function ensureAudio(){try{if(!audio)audio=new (window.AudioContext||window.webkitAudioContext)();if(audio.state==='suspended')audio.resume()}catch(e){}}
function tone(f,t0,dur,vol){const o=audio.createOscillator(),g=audio.createGain();o.type='sine';o.frequency.value=f;
  g.gain.setValueAtTime(0.0001,t0);g.gain.exponentialRampToValueAtTime(vol,t0+0.015);g.gain.exponentialRampToValueAtTime(0.0001,t0+dur);o.connect(g).connect(audio.destination);o.start(t0);o.stop(t0+dur+0.05)}
function chime(l){if(!audio)return;const t=audio.currentTime+0.02;
  if(l===CFGA.lv1){tone(784,t,0.45,0.35);tone(1046.5,t+0.15,0.6,0.3)}else{tone(1046.5,t,0.3,0.4);tone(1318.5,t+0.12,0.3,0.35);tone(1568,t+0.24,0.7,0.35)}}

/* ---------- motor: app + teléfono + árbitro ---------- */
// reloj del simulador: avanza igual que el coche (máx. 50 ms por fotograma), aunque el móvil vaya lento
let core,vp,jd,logLines=[],simT=0,prevN=null;
const now=()=>simT;
function addLog(t,m,cls){logLines.push({t,m,cls});if(logLines.length>300)logLines.shift();if(!pan.hidden)renderLog()}
function boot(){
  core=AnguloCore.create(CFGA);vp=VirtualPhone.create(Object.assign({},CFGV,{seed:(Math.random()*1e6)|0}));
  jd=AnguloJudge.create({lv1:CFGA.lv1,lv2:CFGA.lv2,hyst:CFGA.hyst});
  logLines=[];simT=0;frame.ui=0;
  core.cb.log=(t,m)=>addLog(t,m,/PITIDO/.test(m)?'b':'');
  core.cb.alert=(l,t,a)=>{jd.beep(l,t,a);chime(l);ph.classList.remove('flash');void ph.offsetWidth;ph.classList.add('flash');
    const tr=jd.truth,ok=jd.inMan&&tr!=null&&Math.abs(Math.abs(tr)-l)<6;
    addLog(t,ok?'  ↳ correcto (real '+Math.abs(tr).toFixed(0)+'°)':'  ↳ revisar: '+(jd.inMan?'real '+Math.abs(tr).toFixed(0)+'°':'no había maniobra marcha atrás'),ok?'ok':'bad')};
  core.start(0,CFGV.gps!=='sin');
  addLog(0,'Teléfono '+({vertical:'vertical',horizontal:'apaisado',plano:'tumbado'})[CFGV.mount]+' · GPS '+CFGV.gps+' · vibración '+({0.5:'baja',1:'media',2:'alta'})[CFGV.vib]);
}
boot();
let lastMissN=0;
function frame(n){
  requestAnimationFrame(frame);
  const dms=prevN==null?0:Math.min(n-prevN,50);prevN=n;
  if(typeof ST==='undefined'||ph.hidden||dms<=0)return;
  simT+=dms;
  const t=now(),s={t,psi:ST.th,v:ST.v,x:ST.z,y:ST.x};
  vp.step(s,{orient:core.orient,motion:core.motion,fix:core.fix});jd.step(s);core.tick(t);
  if(t-(frame.ui||0)>60){frame.ui=t;draw(t)}
}
requestAnimationFrame(frame);

/* ---------- pantalla del teléfono ---------- */
const cv=$('vpcv'),ctx=cv.getContext('2d');let shown=0;
const colorFor=a=>(a=Math.abs(a))>=CFGA.lv2?'#f0645a':a>=CFGA.lv1?'#f2b33d':'#5fc7b8';
function rr(x,y,w,h,r){ctx.beginPath();ctx.moveTo(x+r,y);ctx.arcTo(x+w,y,x+w,y+h,r);ctx.arcTo(x+w,y+h,x,y+h,r);ctx.arcTo(x,y+h,x,y,r);ctx.arcTo(x,y,x+w,y,r);ctx.closePath()}
function draw(t){
  const m=core.mode,quiet=m==='drive'||m==='creep',a=quiet?0:core.angle;shown+=(a-shown)*0.5;
  const dpr=Math.min(devicePixelRatio||1,2),W=cv.clientWidth,H=cv.clientHeight;if(cv.width!==W*dpr){cv.width=W*dpr;cv.height=H*dpr}
  ctx.setTransform(dpr,0,0,dpr,0,0);ctx.fillStyle='#151d27';ctx.fillRect(0,0,W,H);ctx.globalAlpha=quiet?.35:1;
  const cx=W/2,cy=H/2,Lc=H*.62,Wc=Lc*.41;
  ctx.lineWidth=1.2;ctx.setLineDash([5,5]);
  [[0,'#8a99a8'],[CFGA.lv1,'#f2b33d'],[-CFGA.lv1,'#f2b33d'],[CFGA.lv2,'#f0645a'],[-CFGA.lv2,'#f0645a']].forEach(([g,c])=>{ctx.save();ctx.translate(cx,cy);ctx.rotate(g*Math.PI/180);ctx.strokeStyle=c;ctx.globalAlpha=(quiet?.35:1)*(g?.35:.6);ctx.beginPath();ctx.moveTo(0,-H);ctx.lineTo(0,H);ctx.stroke();ctx.restore()});
  ctx.setLineDash([]);ctx.globalAlpha=quiet?.35:1;
  ctx.save();ctx.translate(cx,cy);ctx.rotate(shown*Math.PI/180);
  ctx.fillStyle='#05080c';[[-1,-1],[1,-1],[-1,1],[1,1]].forEach(([sx,sy])=>{rr(sx*(Wc/2-Wc*.07)-Wc*.07,sy*(Lc/2-Lc*.22)-Lc*.08,Wc*.14,Lc*.16,2);ctx.fill()});
  ctx.fillStyle='#e8edf2';rr(-Wc/2,-Lc/2,Wc,Lc,Wc*.25);ctx.fill();
  ctx.fillStyle='#4f6a86';ctx.beginPath();ctx.moveTo(-Wc*.40,-Lc*.16);ctx.lineTo(Wc*.40,-Lc*.16);ctx.lineTo(Wc*.33,-Lc*.27);ctx.lineTo(-Wc*.33,-Lc*.27);ctx.closePath();ctx.fill();
  ctx.fillStyle=colorFor(shown);rr(-Wc*.08,-Lc*.08,Wc*.16,Lc*.22,2);ctx.fill();ctx.restore();ctx.globalAlpha=1;
  const st=$('vpst'),kmh=core.kmh(t);
  st.className='vst '+m;st.textContent=m==='always'?'Siempre activo':m==='drive'?'En marcha '+(kmh==null?'sin GPS':Math.round(kmh)+' km/h'):m==='creep'?'Avanzando · callada':m==='stop'?'Listo para aparcar':'Aparcando'+(kmh==null?'':' '+Math.round(kmh)+' km/h');
  const d=$('vpdeg'),v=quiet?'–':Math.round(Math.abs(core.angle));if(d.dataset.v!=v){d.dataset.v=v;d.innerHTML=v+'<small>°</small>'}d.style.color=colorFor(a);
  const aa=Math.max(-45,Math.min(45,shown)),p=Math.abs(aa)/45*50,f=$('vpfill');f.style.width=p+'%';f.style.left=(aa<0?50-p:50)+'%';f.style.background=colorFor(shown);
  const tr=jd.truth;$('vptr').textContent=jd.inMan&&tr!=null?'Real: '+Math.abs(tr).toFixed(0)+'° · app: '+Math.abs(core.angle).toFixed(0)+'°':'Real: sin maniobra';
  const sc=jd.score(),late=sc.miss.filter(e=>t-e.t>1600);
  $('vpok').textContent=sc.acertados;$('vpbad').textContent=sc.fals.filter(g=>t-g.t>1600).length;$('vpmiss').textContent=late.length;
  if(late.length>lastMissN){lastMissN=late.length;const e=late[late.length-1];addLog(t,'⌀ faltó el pitido de '+e.l+'° (la app no pitó)','bad');ph.classList.remove('flash2');void ph.offsetWidth;ph.classList.add('flash2')}
}

/* ---------- panel de ajustes ---------- */
const fmt=(v,st)=>st<1?(+v).toFixed(st<0.1?2:1):Math.round(v);
const SLD=[
 ['kmhDrive','Velocidad de «circulando»','km/h',5,25,1,'Por encima, la app se calla (si dura lo indicado abajo).'],
 ['driveMs','Tiempo para «circulando»','s',1,8,0.5,null,1000],
 ['stopMs','Parada antes de maniobrar','s',0.5,5,0.1,'Tiempo parado para poner el ángulo a 0.',1000],
 ['restK','Sensibilidad «quieto»','×',1.5,4,0.1,'Veces la vibración del ralentí que aún cuenta como parado. Más alto = detecta antes la parada, pero puede confundir ir muy despacio con estar parado.'],
 ['restAcc','Vibración mínima de «quieto»','m/s²',0.05,0.4,0.01],
 ['revV','Sensibilidad de arranque','m/s',0.1,0.6,0.01,'Cuánto tiene que moverse el coche para decidir si va hacia delante o marcha atrás.'],
 ['fwdExitMs','Fin de maniobra al avanzar','s',2,15,0.5,'Avanzando sin parar este tiempo, la maniobra se da por terminada.',1000],
 ['lv1','Primer pitido','°',10,40,1],['lv2','Segundo pitido','°',30,70,1],['hyst','Margen para rearmar','°',1,8,1]
];
function seg(key,opts,obj){return `<div class="seg" data-k="${key}">`+opts.map(([v,l])=>`<button type="button" data-v="${v}" class="${String(obj[key])===String(v)?'on':''}">${l}</button>`).join('')+'</div>'}
function renderPanel(){
  pan.innerHTML=`<button class="close" id="vpx" aria-label="Cerrar">×</button>
<h3>Teléfono virtual</h3>
<div class="row"><span>Posición en el coche</span>${seg('mount',[['vertical','Vertical'],['horizontal','Apaisado'],['plano','Tumbado']],CFGV)}</div>
<div class="row"><span>Inclinación en el soporte</span><b id="vv_tilt">${CFGV.tilt}°</b><input type="range" data-p="tilt" min="0" max="35" step="1" value="${CFGV.tilt}"></div>
<div class="row"><span>Vibración del soporte</span>${seg('vib',[[0.5,'Baja'],[1,'Media'],[2,'Alta']],CFGV)}</div>
<div class="row"><span>GPS</span>${seg('gps',[['bueno','Bueno'],['ciudad','Ciudad'],['sin','Sin GPS']],CFGV)}<em>«Ciudad»: lecturas que faltan y más ruido. «Sin GPS»: garaje.</em></div>
<div class="row"><span>Deriva del giroscopio</span><b id="vv_drift">${CFGV.drift}°/min</b><input type="range" data-p="drift" min="0" max="6" step="0.5" value="${CFGV.drift}"></div>
<h3>Ajustes de la app</h3>
<div class="row"><span>Avisar solo marcha atrás</span>${seg('soloAtras',[[1,'Sí (nueva)'],[0,'No (antigua)']],CFGA)}<em>Con «Sí», la app usa el acelerómetro para saber si arrancas hacia delante (se calla) o marcha atrás (avisa).</em></div>
${SLD.map(([k,l,u,mn,mx,st,em,div])=>{const v=div?CFGA[k]/div:CFGA[k];return `<div class="row"><span>${l}</span><b id="va_${k}">${fmt(v,st)} ${u}</b><input type="range" data-a="${k}" data-div="${div||1}" min="${mn}" max="${mx}" step="${st}" value="${v}">${em?'<em>'+em+'</em>':''}</div>`}).join('')}
<div class="acts"><button type="button" class="pri" id="vpcopy">Copiar ajustes</button><button type="button" id="vpreset">Valores de fábrica</button><button type="button" id="vpre">Reiniciar app</button><button type="button" id="vpclr">Borrar marcador</button></div>
<p class="note">Los cambios se aplican al reiniciar la app (también se reinicia sola al cambiar algo). Pulsa «Copiar ajustes» y pégamelos en el chat para pasarlos a la app del teléfono.</p>
<h3>Registro</h3><div class="log" id="vplog"></div>
<p class="note">✓ pitidos correctos · ✗ pitidos que no tocaban · ⌀ pitidos que faltaron. «Real» es el giro de verdad del coche desde que paraste antes de ir marcha atrás.</p>`;
  renderLog();
}
function renderLog(){const el=$('vplog');if(!el)return;el.innerHTML=logLines.slice(-120).map(l=>`<div class="${l.cls||''}">${(l.t/1000).toFixed(1).padStart(6)}s ${l.m.replace(/</g,'&lt;')}</div>`).join('');el.scrollTop=el.scrollHeight}
let rebootT=0;const softReboot=()=>{clearTimeout(rebootT);rebootT=setTimeout(()=>{boot();lastMissN=0},350)};
pan.addEventListener('click',e=>{
  const b=e.target.closest('button');if(!b)return;
  if(b.id==='vpx'){pan.hidden=true;return}
  const sg=b.closest('.seg');
  if(sg){const k=sg.dataset.k,v=b.dataset.v,obj=k in CFGA?CFGA:CFGV;obj[k]=isNaN(+v)?v:+v;sg.querySelectorAll('button').forEach(x=>x.classList.toggle('on',x===b));save();softReboot();return}
  if(b.id==='vpcopy'){const txt=JSON.stringify(diffCfg());(navigator.clipboard?navigator.clipboard.writeText(txt):Promise.reject()).then(()=>toast('Ajustes copiados')).catch(()=>{prompt('Copia estos ajustes:',txt)});return}
  if(b.id==='vpreset'){Object.assign(CFGA,AnguloCore.DEF);Object.assign(CFGV,VirtualPhone.DEFV);save();renderPanel();softReboot();toast('Valores de fábrica');return}
  if(b.id==='vpre'){boot();lastMissN=0;renderLog();toast('App reiniciada');return}
  if(b.id==='vpclr'){jd=AnguloJudge.create({lv1:CFGA.lv1,lv2:CFGA.lv2,hyst:CFGA.hyst});lastMissN=0;toast('Marcador a cero');return}
});
pan.addEventListener('input',e=>{const r=e.target;if(r.type!=='range')return;
  if(r.dataset.p){CFGV[r.dataset.p]=+r.value;$('vv_'+r.dataset.p).textContent=r.value+(r.dataset.p==='tilt'?'°':'°/min')}
  else{const k=r.dataset.a,dv=+r.dataset.div;CFGA[k]=+r.value*dv;const row=SLD.find(x=>x[0]===k);$('va_'+k).textContent=fmt(r.value,row[5])+' '+row[2]}
  save();softReboot()});
function diffCfg(){const o={};for(const k in AnguloCore.DEF)if(CFGA[k]!==AnguloCore.DEF[k])o[k]=CFGA[k];return {app:o,telefono:CFGV.mount}}
function toast(m){const t=$('toast');if(t&&typeof window.toast!=='function'){t.textContent=m;t.style.opacity=1;clearTimeout(toast.h);toast.h=setTimeout(()=>t.style.opacity=0,1600)}else if(typeof window.toast==='function')window.toast(m)}

/* ---------- botones ---------- */
btn.addEventListener('click',e=>{e.stopPropagation();ensureAudio();UI.open=ph.hidden;ph.hidden=!UI.open;btn.classList.toggle('on',UI.open);if(UI.open){boot();lastMissN=0}else pan.hidden=true;save()});
$('vp0').addEventListener('click',e=>{e.stopPropagation();ensureAudio();core.zero(now())});
$('vpset').addEventListener('click',e=>{e.stopPropagation();ensureAudio();if(pan.hidden){renderPanel();pan.hidden=false}else pan.hidden=true});
$('vpsz').addEventListener('click',e=>{e.stopPropagation();UI.big=!UI.big;ph.classList.toggle('big',UI.big);save()});
['pointerdown','touchstart','mousedown','wheel'].forEach(ev=>{ph.addEventListener(ev,e=>e.stopPropagation(),{passive:true});pan.addEventListener(ev,e=>e.stopPropagation(),{passive:true})});
document.addEventListener('pointerdown',ensureAudio,{once:true});
})();
