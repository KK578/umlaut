#!/usr/bin/env node

const path = require('path');
const program = require('commander');
const yeoman = require('yeoman-environment');

const umlParser = require('../uml-parser/index.js');
const inputGenerator = require('../input-generator/index.js');
const promises = require('../util/promises.js');

const yeomanEnv = yeoman.createEnv();

yeomanEnv.register(path.join(__dirname, '../generators/app'), 'umlaut:app');

///////////////////////////////////////////////////////////
// Utility functions
function promiseRunTestGenerator(options) {
	return new Promise((resolve, reject) => {
		yeomanEnv.run('umlaut:app', options, (err) => {
			if (err) {
				reject();
			}
			else {
				resolve();
			}
		});
	});
}

function run(filename) {
	return umlParser(filename).then((parsedModelData) => {
		console.log('Model Parsed!');

		return inputGenerator(parsedModelData);
	}).then((modelDataWithInputs) => {
		console.log('Inputs Generated!');

		const options = {
			model: JSON.stringify(modelDataWithInputs)
		};

		return promiseRunTestGenerator(options);
	});
}

///////////////////////////////////////////////////////////
// CLI
const packageData = require('../package.json');

program.version(packageData.version)
	.usage('[options] <file>')
	.option('-f, --framework <framework>', 'Testing Language+Framework to generate tests for')
	.parse(process.argv);

run(program.args[0]);
