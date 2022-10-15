// --------------------------------------------------------------------------
// --- Icons Markdown Gallery Generator
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

console.log();

// --- Gallery (per section) -----------------------------------------

for ( var s = 0 ; s < index.length ; s++ ) {
  const section = index[s] ;
  console.log( '<hr/>' );
  console.log();
  console.log( `## ${section}` );
  console.log();
  console.log( `  <div class="database">` );

  const content = sections[section] ;
  content.sort();

  for( var k = 0 ; k < content.length ; k++ ) {
    const name = content[k];
    const icon = icons[name];
    const title = icon.title || name ;
    console.log( `<div class="icon-block" title="${title}">`);
    console.log( `<div class="icon-name refname" id="ICON.${name}">${name}</div>` );
    console.log( `<svg class="icon-svg" viewBox="${icon.viewBox}">` );
    console.log( `<path d="${icon.path}"/>`);
    console.log( `</svg>` );
    console.log( `</div>` );
  }
  console.log( `</div>`);
  console.log();
}

// -------------------------------------------------------------------
