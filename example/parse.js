var parser = require('../');
var p = new Parser(function (results) {
    console.dir(results);
});
process.stdin.pipe(p);
