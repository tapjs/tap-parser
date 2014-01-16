var test = require('tape');
var parser = require('../');

var lines = [
    'TAP version 13',
    '1..4',     // test with plan at the top, since that reveals edge cases for extra lines
    '# beep',
    'ok 1 should be equal',
    '  extra1',
    '  extra2',
    'ok 2 should be equivalent',
    '# boop',
    '  extra1',
    'ok 3 should be equal',
    '# comment1',
    '# comment2',
    'ok 4 (unnamed assert)',
    '',
    '# tests 4',
    '# pass  4',
    '',
    '# ok'
];

var expected = { asserts: [], comments: [] };

expected.comments = [ 'beep', 'boop', 'comment1', 'comment2', 'tests 4', 'pass  4', 'ok' ];

expected.asserts.push({
    ok: true,
    number: 1,
    name: 'should be equal',
    extra: '  extra1\n  extra2\n'
});
expected.asserts.push({
    ok: true,
    number: 2,
    name: 'should be equivalent',
    extra: '# boop\n  extra1\n'
});
expected.asserts.push({
    ok: true,
    number: 3,
    name: 'should be equal',
    extra: '# comment1\n# comment2\n'
});
expected.asserts.push({
    ok: true,
    number: 4,
    name: '(unnamed assert)',
    extra: '\n'
});

test('extra lines', function (t) {
    t.plan(4 * 2 + 1 + 4 * 2 + 7);
    
    var p = parser(onresults);
    p.on('results', onresults);
    
    var asserts = [];
    p.on('assert', function (assert) {
        asserts.push(assert);
    });
    
    p.on('plan', function (plan) {
        t.same(plan, { start: 1, end: 4 });
    });
    
    p.on('comment', function (c) {
        t.equal(c, expected.comments.shift());
    });
    
    for (var i = 0; i < lines.length; i++) {
        p.write(lines[i] + '\n');
    }
    p.end();
    
    function onresults (results) {
        t.ok(results.ok);
        t.same(results.errors, []);
        t.same(asserts.length, 4);
        t.same(results.asserts, asserts);
        asserts.forEach(function(assert, index) {
            t.same(assert, expected.asserts[index]);
        });
    }
});

