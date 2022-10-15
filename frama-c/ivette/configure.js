// --------------------------------------------------------------------------
// --- Configure Packages
// --- Called by [make pkg]
// --------------------------------------------------------------------------

const path = require('path');
const fs = require('fs');

const loader = process.argv[2];
const inputFiles = process.argv.slice(3);
const packages = new Map();
let buffer = '// Ivette Package Loader (generated)\n';

inputFiles.forEach((file) => {
  try {
    const pkgId = path.relative('./src',path.dirname(file));
    const pkgSrc = fs.readFileSync(file, { encoding: 'UTF-8' });
    const pkgJson = JSON.parse(pkgSrc);
    packages.set(pkgId,pkgJson);
  } catch(err) {
    console.error(`[Dome] Error ${file}: ${err}`);
    process.exit(1);
  }
});

function depend(id) {
  const pkg = packages.get(id);
  if (pkg) configure(pkg,id);
}

function configure(pkg, id) {
  if (!pkg.done) {
    pkg.done = true;
    for(let parent = id;;) {
      parent = path.dirname(parent);
      if (!parent || parent === '.') break;
      depend(parent);
    }
    const { depends=[], main='.' } = pkg;
    depends.forEach(depend);
    console.log(`[Ivette] package ${id}`);
    buffer += `import '${path.join(id,main)}';\n`;
  }
}

packages.forEach(configure);
fs.writeFileSync(loader, buffer);
