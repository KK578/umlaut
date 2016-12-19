const chai = require('chai');
const helpers = require('yeoman-test');
const assert = require('yeoman-assert');
const path = require('path');
const expect = chai.expect;


describe.only('model-driven-testing:nunit test/fixtures/test-generator/uml/ test/fixtures/test-generator/smt/', () => {
	beforeEach(() => {
		return helpers.run(path.join(__dirname, '../../generators/nunit'))
			.inDir('test/tmp/')
			.withArguments([
				'../fixtures/test-generator/uml/',
				'../fixtures/test-generator/smt/'
			]);
	});

	it('should make a test suite for SimpleMath', () => {
		assert.file('build/SimpleMathTest.cs');
	});
});
