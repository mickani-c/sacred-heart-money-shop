(function(root){
'use strict';
const VALUES=[1,2,5,10,20,50,100,100,200,500,1000,5000,10000];
const LABELS=['1角','2角','5角','1元','2元','5元','10元','10元','20元','50元','100元','500元','1000元'];
const NAMES=[['糖果','餅乾','果汁','清水','筆記簿','鉛筆','橡皮擦','直尺','白膠漿','紙巾'],['書包','籃球','電風扇','吸塵機','平板電腦','耳機','手錶','運動鞋','相機','保溫水樽']];
const UNITS=[['包','包','盒','瓶','本','枝','塊','把','樽','包'],['個','個','部','部','部','副','隻','對','部','個']];
const PRICES=[[22,40,50,30,60,20,15,35,45,25],[2680,1280,3980,12800,24800,1995,3680,4590,16800,1295]];
function defaults(){return {version:1,uniform:'auto',stores:[0,1].map((s)=>({products:PRICES[s].map((price,i)=>({price,on:i<6})),minimum:false,denominationMode:'manual',allowed:VALUES.map((_,i)=>s===1||i<7),walletMode:'unlimited',stocks:VALUES.map((_,i)=>i<7?10:5)}))};}
const copy=x=>JSON.parse(JSON.stringify(x));
function validate(input){
 if(!input||input.version!==1||!['auto','summer','winter'].includes(input.uniform)||!Array.isArray(input.stores)||input.stores.length!==2)throw Error('設定檔格式不正確。');
 const out=defaults();out.uniform=input.uniform;
 input.stores.forEach((s,l)=>{let d=out.stores[l];
  if(!s||!Array.isArray(s.products)||s.products.length!==10)throw Error('貨品設定不完整。');
  d.products=s.products.map(p=>{if(!p||!Number.isInteger(p.price)||p.price<1||p.price>99999||typeof p.on!=='boolean')throw Error('貨品價錢須為0.10至9999.90元。');return {price:p.price,on:p.on};});
  let count=d.products.filter(p=>p.on).length;if(count<1||count>6)throw Error('每間店舖須選擇1至6款貨品上架。');
  if(!['manual','random'].includes(s.denominationMode)||!['unlimited','manual','random'].includes(s.walletMode)||typeof s.minimum!=='boolean')throw Error('遊戲條件不正確。');
  d.minimum=s.minimum;d.denominationMode=s.denominationMode;d.walletMode=s.walletMode;
  if(!Array.isArray(s.allowed)||s.allowed.length!==13||s.allowed.some(x=>typeof x!=='boolean'))throw Error('可用貨幣設定不完整。');
  d.allowed=s.allowed.map((v,i)=>v&&(l===1||i<7));
  if(s.denominationMode==='manual'&&!d.allowed.some(Boolean))throw Error('請至少選擇一款可用貨幣。');
  if(!Array.isArray(s.stocks)||s.stocks.length!==13||s.stocks.some(x=>!Number.isInteger(x)||x<0||x>200))throw Error('每款貨幣數量須為0至200。');d.stocks=s.stocks.slice();
 });return out;
}
// All amounts are integer tenths of a dollar. Bounded minimum-count change:
// residue-class monotone queues, O(denominations * target), with reconstruction.
function solve(target,allowed,stocks=null){
 if(!Number.isInteger(target)||target<0||target>300000)return null;
 let old=new Int32Array(target+1);old.fill(1000000);old[0]=0;let choices=[];
 for(let i=0;i<13;i++){
  let v=VALUES[i],lim=allowed[i]?(stocks?stocks[i]:Math.floor(target/v)):0;
  if(!lim){choices.push(null);continue;}
  let next=new Int32Array(target+1);next.fill(1000000);let use=new Int32Array(target+1);
  let q=new Int32Array(Math.floor(target/v)+2);
  for(let r=0;r<v&&r<=target;r++){
   let head=0,tail=0;
   for(let k=0,a=r;a<=target;k++,a+=v){
    while(head<tail&&q[head]<k-lim)head++;
    let score=old[a]-k;
    while(head<tail&&old[r+q[tail-1]*v]-q[tail-1]>=score)tail--;
    q[tail++]=k;let best=q[head];next[a]=old[r+best*v]+k-best;use[a]=k-best;
   }
  }old=next;choices.push(use);
 }
 if(old[target]>=1000000)return null;let counts=Array(13).fill(0),a=target;
 for(let i=12;i>=0;i--){if(choices[i]){counts[i]=choices[i][a];a-=counts[i]*VALUES[i];}}
 return a===0?{count:old[target],counts}:null;
}
function noBorrow(a,b){if(a<b)return false;while(a||b){if(a%10<b%10)return false;a=Math.floor(a/10);b=Math.floor(b/10);}return true;}
function sequential(pay,prices){for(const p of prices){if(!noBorrow(pay,p))return false;pay-=p;}return true;}
function digitSafe(prices){let carry=prices.slice();while(carry.some(v=>v>0)){if(carry.reduce((s,v)=>s+v%10,0)>9)return false;carry=carry.map(v=>Math.floor(v/10));}return true;}
function rand(n,rng){return Math.floor(rng()*n);}
function shuffle(a,rng){a=a.slice();for(let i=a.length-1;i>0;i--){let j=rand(i+1,rng);[a[i],a[j]]=[a[j],a[i]];}return a;}
function generate(config,level,role,previousSignature='',rng=Math.random){
 const s=config.stores[level],all=VALUES.map((_,i)=>level===1||i<7),goods=s.products.map((p,i)=>({...p,i})).filter(p=>p.on);
 if(!goods.length||goods.length>6)return {error:'請先選擇1至6款貨品上架。'};
 let maxStock=s.walletMode==='manual'?s.stocks.reduce((n,c,i)=>n+(all[i]&&s.allowed[i]?c*VALUES[i]:0),0):Infinity;
 let fallback=null;
 for(let attempt=0;attempt<180;attempt++){
  const first=goods[rand(goods.length,rng)];let cart=[first.i];
  if(level===0&&rng()<.5){const same=goods.filter(p=>p.price===first.price);let second=same[rand(same.length,rng)];if(digitSafe([first.price,second.price]))cart.push(second.i);}
  if(level===1){let n=1+rand(3,rng);while(cart.length<n)cart.push(goods[rand(goods.length,rng)].i);}
  let prices=cart.map(i=>s.products[i].price),total=prices.reduce((a,b)=>a+b,0);
  let allowed=s.denominationMode==='manual'?s.allowed.slice():all.map(v=>v&&rng()<.63);
  if(!allowed.some(Boolean))allowed[rand(level?13:7,rng)]=true;
  let paid=total,target=total;
  if(role==='cashier'){
   if(level===0){
    // Construct a no-borrow payment digit by digit, then verify every step.
    let v=total,place=1;paid=0;
    while(v||place<=100){let digit=v%10;paid+=(digit+(place>=100&&total<100?0:rand(10-digit,rng)))*place;v=Math.floor(v/10);place*=10;}
    if(!sequential(paid,prices))continue;
   }else{let step=total>10000?5000:1000;paid=Math.ceil(total/step)*step+(rng()<.3?step:0);}
   target=paid-total;
  }
  if(target>maxStock&&s.walletMode==='manual'&&s.denominationMode==='manual')continue;
  const unrestricted=solve(target,allowed);if(!unrestricted)continue;
  let stocks=null;
  if(s.walletMode==='manual')stocks=s.stocks.map((v,i)=>allowed[i]?v:0);
  if(s.walletMode==='random')stocks=allowed.map((v,i)=>v?unrestricted.counts[i]+rand(i<7?7:4,rng):0);
  const optimal=stocks?solve(target,allowed,stocks):unrestricted;if(!optimal)continue;
  // Avoid impractically long exercises without silently changing the teacher's settings.
  if(optimal.count>120)continue;
  const incoming=solve(paid,all);if(!incoming||incoming.count>120)continue;
  const signature=JSON.stringify([allowed,stocks]);
  const q={cart,total,paid,target,prices,allowed,stocks,optimal,incoming,signature};
  if((s.denominationMode==='random'||s.walletMode==='random')&&signature===previousSignature){fallback=q;continue;}
  return q;
 }
 return fallback||{error:'目前的上架價錢及貨幣條件未能產生合適題目。請增加可用貨幣或數量，或調整貨品價錢後再試。'};
}
const api={VALUES,LABELS,NAMES,UNITS,defaults,validate,copy,solve,noBorrow,sequential,digitSafe,generate};
if(typeof module!=='undefined'&&module.exports)module.exports=api;else root.MoneyEngine=api;
})(typeof globalThis!=='undefined'?globalThis:this);
