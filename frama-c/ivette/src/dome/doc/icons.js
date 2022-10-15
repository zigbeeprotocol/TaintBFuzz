// --------------------------------------------------------------------------
// --- Icons Gallery Generator
// --------------------------------------------------------------------------

const path = require('path');
const icons = require(path.resolve( process.argv[2] ));
const index = [];
const sections = {};

// --- Indexing & Sectioning -----------------------------------------

for ( var name in icons ) {
  const icon = icons[name];
  const section = icon.section || "Others" ;
  if (section != "Others" && index.indexOf(section) < 0) index.push( section );
  var content = sections[section] ;
  if (!content) sections[section] = content = [] ;
  content.push(name) ;
}

index.sort();
if (sections["Others"]) index.push("Others");

console.log( `<div id="main">` );

// --- Gallery (per section) -----------------------------------------

console.log( `<div id="content">` );
console.log( `<div id="page">` );
console.log( `  <h1 class="page-title">Icons Gallery</h1>` );

for ( var s = 0 ; s < index.length ; s++ ) {
  const section = index[s] ;
  console.log( `<section>` );
  console.log( `<article><h4 id="SECTION.${section}">${section}</h4>` );
  console.log( `  <div class="database">` );

  const content = sections[section] ;
  content.sort();

  for( var k = 0 ; k < content.length ; k++ ) {
    const name = content[k];
    const icon = icons[name];
    const title = icon.title || name ;
    console.log( `  <div class="icon-block" onclick="window.location.href='#ICON.${name}'" title="${title}">`);
    console.log( `    <div class="icon-name refname" id="ICON.${name}">${name}</div>` );
    console.log( `    <svg class="icon-svg" viewBox="${icon.viewBox}">` );
    console.log( `      <path d="${icon.path}"/>`);
    console.log( `    </svg>` );
    console.log( `  </div>` );
  }
  console.log( `  </div>` );
  console.log( `</article>` );
  console.log( `</section>` );
}

console.log( `</div>` ); // #content
console.log( `</div>` ); // #page

// --- Navigation Bar ------------------------------------------------

console.log( `<div id="index">` );
console.log( `<nav>` );
console.log( `<h2><a href="index.html">Dome</a></h2>` );
console.log( `<h3>Classes</h3>` );
console.log( `<ul><li><a href="module-dome_controls_icons.Icon.html">Icon (Component)</a></li>` );
for ( var s=0; s < index.length ; s++ ) {
  const section = index[s];
  console.log( `  <li><a href="#SECTION.${section}">${section}</a></li>` );
}
console.log( `</ul>` );
console.log( `<h3>Icons</h3><ul>` );
for( var name in icons ) {
  console.log( `<li><a href="#ICON.${name}">${name}</a></li>` );
}
console.log( `</ul>`);
console.log( `</nav>` );
console.log( `</div>` ); // #index

console.log( `</div>` ); // #main

// -------------------------------------------------------------------
