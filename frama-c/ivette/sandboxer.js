// --------------------------------------------------------------------------
// --- Configure Sandboxes
// --- Called by [make pkg]
// --------------------------------------------------------------------------

const path = require('path');
const fs = require('fs');

const loader = process.argv[2];
const inputFiles = process.argv.slice(3);
let buffer = '// Ivette Sandboxes Loader (generated)\n';

inputFiles.forEach((file) => {
  try {
    const box = path.relative('./src',file);
    console.log(`[Ivette] sandbox ${box}`);
    buffer += `import '../${box}';\n`;
  } catch(err) {
    console.error(`[Dome] Error ${file}: ${err}`);
    process.exit(1);
  }
});

fs.writeFileSync(loader, buffer);
