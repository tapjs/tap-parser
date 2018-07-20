#!/usr/bin/env node
var Parser = require('../')
var etoa = require('events-to-array')
var util = require('util')
var fs = require('fs')
var Path = require('path')
var commandLineArgs = require('command-line-args')
var yaml = require('js-yaml')

var option = commandLineArgs([
  { name: 'json', alias: 'j', type: Number },
  { name: 'tap', alias: 't', type: Boolean },
  { name: 'bail', alias: 'b', type: Boolean },
  { name: 'ignore-all-whitespace', alias: 'w', type: Boolean },
  { name: 'omit-version', alias: 'o', type: Boolean },
  { name: 'version', alias: 'v', type: Boolean },
  { name: 'help', alias: 'h', type: Boolean },
])

if (option.version) return version()
if (option.help) return usage()

if (option.json === null) option.json = 2

var parser = new Parser({
  bail: option.bail,
  preserveWhitespace: !option['ignore-all-whitespace'],
  omitVersion: option['omit-version'],
})
var events = etoa(parser, [ 'pipe', 'unpipe', 'prefinish', 'finish', 'line' ])

process.stdin.pipe(parser)
if (option.lines)
  parser.on('line', function (l) {
    process.stdout.write(l)
  })
else
  process.on('exit', function () {
    console.log(format(events))
    if (!parser.ok)
      process.exit(1)
  })

function tapFormat (msg, indent) {
  return indent + msg.map(function (item) {
    switch (item[0]) {
      case 'child':
        var comment = item[1][0]
        var child = item[1].slice(1)
        return tapFormat([comment], '') + tapFormat(child, '    ')

      case 'version':
        return 'TAP version ' + item[1] + '\n'

      case 'plan':
        var p = item[1].start + '..' + item[1].end
        if (item[1].comment)
          p += ' # ' + item[1].comment
        return p + '\n'

      case 'pragma':
        return 'pragma ' + (item[2] ? '+' : '-') + item[1] + '\n'

      case 'bailout':
        var r = item[1] === true ? '' : (' ' + item[1])
        return 'Bail out!' + r + '\n'

      case 'assert':
        var res = item[1]
        return (res.ok ? '' : 'not ') + 'ok ' + res.id +
          (res.name ? ' - ' + res.name.replace(/ \{$/, '') : '') +
          (res.skip ? ' # SKIP' +
            (res.skip === true ? '' : ' ' + res.skip) : '') +
          (res.todo ? ' # TODO' +
            (res.todo === true ? '' : ' ' + res.todo) : '') +
          (res.time ? ' # time=' + res.time + 'ms' : '') +
          '\n' +
          (res.diag ?
            '  ---\n  ' +
            yaml.safeDump(res.diag).split('\n').join('\n  ').trim() +
            '\n  ...\n'
            : '')

      case 'extra':
      case 'comment':
        return item[1]
    }
  }).join('').replace(/\n/g, '\n' + indent).trim() + '\n'
}

function format (msg) {
  if (option.tap)
    return tapFormat(msg, '')
  else if (option.json)
    return JSON.stringify(msg, null, option.json)
  else
    return util.inspect(events, null, Infinity)
}

function usage () {
  var usagePath = Path.resolve(__dirname, 'usage.txt');
  console.log(fs.readFileSync(usagePath, { encoding: 'utf8' }));

  if (!process.stdin.isTTY) process.stdin.resume()
}

function version () {
  console.log(require('../package.json').version)
}
