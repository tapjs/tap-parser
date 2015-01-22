var test = require('tape');
var parser = require('../');

var lines = [
    'TAP version 13',
    '# beep',
    'ok 1 should be equal',
    '',
    'ok 2 should be equivalent',
    '# boop',
    'ok 3 should be equal',
    ' ---',
    ' foo: "bar"',
    ' ...',
    'ok 4 (unnamed assert)',
    '',
    'not ok 5 diag with three chars',
    ' ---',
    '  operator: deepEqual',
    '  expected:',
    '   {}',
    '  actual:',
    '   {foo: "bar"}',
    ' ...',
    '1..5',
    '# tests 5',
    '# pass  4',
    '# fail 1',
    '',
    '# not ok'
];

var expected = { asserts: [], comments: [], diags: [] };

expected.comments = [ 'beep', 'boop', 'tests 5', 'pass  4', 'fail 1', 'not ok' ];

expected.asserts.push({
    ok: true,
    number: 1,
    name: 'should be equal'
});
expected.asserts.push({
    ok: true,
    number: 2,
    name: 'should be equivalent'
});
expected.asserts.push({
    ok: true,
    number: 3,
    name: 'should be equal'
});
expected.asserts.push({
    ok: true,
    number: 4,
    name: '(unnamed assert)'
});
expected.asserts.push({
    ok: false,
    number: 5,
    name: 'diag with three chars'
});

expected.diags.push({
    foo: 'bar'
});
expected.diags.push({
    operator: 'deepEqual',
    actual: {foo: 'bar'},
    expected: {}
});

test('simple ok', function (t) {
    t.plan(5 * 2 + 2 + 4 + 5 + 1);

    var p = parser(onresults);
    p.on('results', onresults);

    var asserts = [];
    p.on('assert', function (assert) {
        asserts.push(assert);
        t.same(assert, expected.asserts.shift(), 'assert should be the same');
    });

    var diags = [];
    p.on('diag', function (diag) {
        diags.push(diag);
        t.same(diag, expected.diags.shift(), 'diag should be the same');
    });

    p.on('plan', function (plan) {
        t.same(plan, { start: 1, end: 5 }, 'plan should be the same');
    });

    p.on('comment', function (c) {
        t.equal(c, expected.comments.shift(), 'comment should be equal');
    });

    for (var i = 0; i < lines.length; i++) {
        p.write(lines[i] + '\n');
    }
    p.end();

    function onresults (results) {
        t.notOk(results.ok, 'tests should not be ok due to one failed test');
        t.same(results.errors, [], 'errors should be the same');
        t.same(asserts.length, 5, 'asserts length should be the same');
        t.same(results.asserts, asserts, 'asserts should be the same');
    }
});
