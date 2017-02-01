const path = require('path');

const umlParser = require('../uml-parser/index.js');
const inputGenerator = require('../input-generator/index.js');

const yeoman = require('yeoman-environment');
const yeomanEnv = yeoman.createEnv();
yeomanEnv.register(path.join(__dirname, '../generators/app'), 'mdt:app');

function promiseRunTestGenerator(options) {
	return new Promise((resolve, reject) => {
		yeomanEnv.run('mdt:app', options, (err) => {
			if (err) {
				reject();
			}
			else {
				resolve();
			}
		});
	});
}

describe('Integration Test', function () {
	it('should successfully build SimpleMath test fixture', function () {
		const fixture = global.fixtures.FullModels.SimpleMath.uml;

		return umlParser(fixture).then((parsedModelData) => {
			return inputGenerator(parsedModelData);
		}).then((modelDataWithInputs) => {
			const options = {
				model: JSON.stringify(modelDataWithInputs),
				framework: 'nunit'
			};

			return promiseRunTestGenerator(options);
		});
	});
});
