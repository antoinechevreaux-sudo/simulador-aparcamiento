const C='aparcar-v158',F=['./','./index.html','./manifest.webmanifest','./icon-192.png','./icon-512.png','./car_bmw.glb','./car_x7.glb','./angulo-sim.js'];
self.addEventListener('install',e=>{e.waitUntil(caches.open(C).then(c=>c.addAll(F)));self.skipWaiting()});
self.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(k=>Promise.all(k.filter(x=>x!==C).map(x=>caches.delete(x)))));self.clients.claim()});
self.addEventListener('fetch',e=>{e.respondWith(caches.match(e.request,{ignoreSearch:true}).then(r=>r||fetch(e.request).then(n=>{if(n.ok&&/\.glb$/.test(new URL(e.request.url).pathname)){const c=n.clone();caches.open(C).then(x=>x.put(e.request,c))}return n})))});
