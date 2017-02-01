const path = require('path');

const umlParser = require('../uml-parser/index.js');
const inputGenerator = require('../input-generator/index.js');

const yeoman = require('yeoman-environment');
const yeomanEnv = yeoman.createEnv();
yeomanEnv.register(path.join(__dirname, '../generators/app'), 'mdt:app');

describe('Integration Test', function () {
	it('should successfully build SimpleMath test fixture', function (done) {
		const fixture = global.fixtures.FullModels.SimpleMath.uml;

		umlParser(fixture).then((data) => {
			return inputGenerator(data);
		}).then((data) => {
			const model = JSON.stringify(data);
			console.log(model);

			yeomanEnv.run('mdt:app', { model, framework: 'nunit' }, done);
		});
	});
});
