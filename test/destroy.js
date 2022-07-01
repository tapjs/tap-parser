const Parser = require('../')
const t = require('tap')

t.test('destroy()', function (t) {
  const stream = new Parser()
  stream.destroy()
  t.pass('destroyed')
  t.end()
})
