/*! Spacefast remix CTA — load once; edit this file to update every host page.
 *  <script src="https://badge-playground.space.fast/remix-cta.js" defer></script>
 *  Optional: data-href, data-bounce="false" to disable, data-label
 */
(function () {
  if (window.__sfRemixCta) return;
  window.__sfRemixCta = true;
  var script = document.currentScript;
  var href = (script && script.getAttribute("data-href")) || "https://spacefast.com";
  var label = (script && script.getAttribute("data-label")) || "Remix on";
  var bounceAttr = script && script.getAttribute("data-bounce");
  var bounceOn = bounceAttr != null
    ? !/^(0|false|no|off)$/i.test(bounceAttr)
    : !/^(0|false|no|off)$/i.test(new URLSearchParams(location.search).get("bounce") || "true");
  var reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  var css = ':root{--sf-remix-canvas:#f7f5ef;--sf-remix-ink:#0c0c0c;--sf-remix-marker:#d8f24b}.sf-remix-cta{--rot:-2.2deg;position:fixed;right:28px;bottom:28px;left:auto;top:auto;z-index:2147483000;display:inline-flex;align-items:center;gap:0.08em;margin:0;padding:0.42em 0.72em 0.48em 0.78em;text-decoration:none;color:var(--sf-remix-ink);font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;font-size:clamp(20px,2.8vw,24px);font-weight:560;letter-spacing:-0.03em;line-height:1.05;white-space:nowrap;cursor:pointer;touch-action:manipulation;transform:rotate(var(--rot));background-image:url("https://spacefast.com/_astro/static/scene/marker.646c1ea6cbc9.svg");background-repeat:no-repeat;background-position:50% calc(50% + 0.06em);background-size:100% 1.15em;-webkit-tap-highlight-color:transparent;filter:drop-shadow(0 1px 0 rgba(12,12,12,0.04));box-sizing:border-box}.sf-remix-cta:focus-visible{outline:2px solid var(--sf-remix-ink);outline-offset:6px}.sf-remix-cta.is-bounce{right:auto;bottom:auto}.sf-remix-cta .sf-remix-label{position:relative;z-index:1;font-size:0.72em;font-weight:500;letter-spacing:-0.02em;opacity:0.92;line-height:1;display:inline-flex;align-items:center;height:1em}.sf-remix-cta .sf-remix-wordmark{position:relative;z-index:1;display:inline-flex;align-items:center;height:1em}.sf-remix-cta .sf-remix-wordmark img{display:block;height:100%;width:auto}.sf-remix-fx{position:fixed;inset:0;pointer-events:none;z-index:2147482999;overflow:hidden}.sf-remix-fx .fx-bit{position:absolute;left:0;top:0;color:var(--sf-remix-ink);opacity:0.9;will-change:transform,opacity;animation:sf-remix-pop var(--dur,700ms) cubic-bezier(.12,.7,.22,1) forwards;transform:translate(-50%,-50%) rotate(var(--spin,0deg));font-size:var(--size,12px);line-height:1}@keyframes sf-remix-pop{0%{opacity:0.95;transform:translate(-50%,-50%) rotate(var(--spin,0deg)) scale(0.4)}70%{opacity:0.85}100%{opacity:0;transform:translate(calc(-50% + var(--dx)),calc(-50% + var(--dy))) rotate(calc(var(--spin,0deg) + var(--twist,40deg))) scale(1)}}@media (prefers-reduced-motion:reduce){.sf-remix-fx .fx-bit{animation:none;opacity:0}}';

  var style = document.createElement("style");
  style.textContent = css;
  document.head.appendChild(style);

  var fx = document.createElement("div");
  fx.className = "sf-remix-fx";
  fx.setAttribute("aria-hidden", "true");
  document.body.appendChild(fx);

  var el = document.createElement("a");
  el.className = "sf-remix-cta";
  el.href = href;
  el.target = "_blank";
  el.rel = "noopener noreferrer";
  el.setAttribute("aria-label", label + " Spacefast");
  el.innerHTML = '<span class="sf-remix-label"></span><span class="sf-remix-wordmark" aria-hidden="true"><img src="https://spacefast.com/_astro/static/brand/spacefast-wordmark.f88ca285b34f.svg" alt="" height="100%" style="display:block;height:100%;width:auto" /></span>';
  el.querySelector(".sf-remix-label").textContent = label;
  document.body.appendChild(el);

  var SHAPES = ["*", "+", "~", "x", "o", "-"];
  var COLORS = ["#0c0c0c", "#d8f24b", "#6e6a5e"];
  var hovering = false, lastSpawn = 0, trailX = 0, trailY = 0;
  function spawnBurst(x, y, count) {
    if (reduceMotion) return;
    for (var i = 0; i < count; i++) {
      var bit = document.createElement("span");
      bit.className = "fx-bit";
      bit.textContent = SHAPES[(Math.random() * SHAPES.length) | 0];
      var angle = Math.random() * Math.PI * 2;
      var dist = 28 + Math.random() * 54;
      bit.style.left = x + "px";
      bit.style.top = y + "px";
      bit.style.color = COLORS[(Math.random() * COLORS.length) | 0];
      bit.style.setProperty("--dx", (Math.cos(angle) * dist).toFixed(1) + "px");
      bit.style.setProperty("--dy", (Math.sin(angle) * dist - 8).toFixed(1) + "px");
      bit.style.setProperty("--spin", ((Math.random() * 80) - 40).toFixed(1) + "deg");
      bit.style.setProperty("--twist", ((Math.random() * 140) - 70).toFixed(1) + "deg");
      bit.style.setProperty("--dur", (520 + Math.random() * 420).toFixed(0) + "ms");
      bit.style.setProperty("--size", (9 + Math.random() * 11).toFixed(1) + "px");
      fx.appendChild(bit);
      bit.addEventListener("animationend", function () { bit.remove(); });
    }
  }
  el.addEventListener("pointerenter", function (e) {
    hovering = true; trailX = e.clientX; trailY = e.clientY; spawnBurst(e.clientX, e.clientY, 10);
  });
  el.addEventListener("pointerleave", function () { hovering = false; });
  el.addEventListener("pointermove", function (e) {
    if (!hovering) return;
    var now = performance.now();
    if (Math.hypot(e.clientX - trailX, e.clientY - trailY) > 10 && now - lastSpawn > 55) {
      lastSpawn = now; trailX = e.clientX; trailY = e.clientY;
      spawnBurst(e.clientX, e.clientY, 3 + ((Math.random() * 3) | 0));
    }
  });

  function placeAt(left, top) {
    var rect = el.getBoundingClientRect();
    var L = Math.min(Math.max(8, window.innerWidth - rect.width - 8), Math.max(8, left));
    var T = Math.min(Math.max(8, window.innerHeight - rect.height - 8), Math.max(8, top));
    el.style.left = L + "px"; el.style.top = T + "px"; el.style.right = "auto"; el.style.bottom = "auto";
  }
  var bounce = { x: 0, y: 0, vx: 1.0, vy: 0.82 };
  if (bounceOn && !reduceMotion) {
    el.classList.add("is-bounce");
    requestAnimationFrame(function () {
      var rect = el.getBoundingClientRect();
      bounce.x = Math.max(8, window.innerWidth - rect.width - 28);
      bounce.y = Math.max(8, window.innerHeight - rect.height - 28);
      placeAt(bounce.x, bounce.y);
      bounce.vx = (Math.random() < 0.5 ? -1 : 1) * (0.85 + Math.random() * 0.35);
      bounce.vy = (Math.random() < 0.5 ? -1 : 1) * (0.7 + Math.random() * 0.35);
      var last = performance.now();
      function tick(now) {
        var dt = Math.min(32, now - last) / 16.67; last = now;
        var rect = el.getBoundingClientRect();
        var maxX = Math.max(8, window.innerWidth - rect.width - 8);
        var maxY = Math.max(8, window.innerHeight - rect.height - 8);
        bounce.x += bounce.vx * dt * 1.2;
        bounce.y += bounce.vy * dt * 1.2;
        if (bounce.x <= 8) { bounce.x = 8; bounce.vx = Math.abs(bounce.vx); }
        if (bounce.x >= maxX) { bounce.x = maxX; bounce.vx = -Math.abs(bounce.vx); }
        if (bounce.y <= 8) { bounce.y = 8; bounce.vy = Math.abs(bounce.vy); }
        if (bounce.y >= maxY) { bounce.y = maxY; bounce.vy = -Math.abs(bounce.vy); }
        el.style.left = bounce.x + "px"; el.style.top = bounce.y + "px";
        el.style.right = "auto"; el.style.bottom = "auto";
        requestAnimationFrame(tick);
      }
      requestAnimationFrame(tick);
    });
  }
})();

