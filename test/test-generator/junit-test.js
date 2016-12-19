const chai = require('chai');
const helpers = require('yeoman-test');
const assert = require('yeoman-assert');
const path = require('path');
const expect = chai.expect;

describe('Test Generator JUnit', () => {
	beforeEach(() => {
		return helpers.run(path.join(__dirname, '../../generators/junit'))
			.inDir('test/tmp/junit/')
			.withArguments([
				'../../fixtures/test-generator/uml/',
				'../../fixtures/test-generator/smt/'
			]);
	});

	it('should make a test suite for SimpleMath', () => {
		assert.file('build/SimpleMathTest.java');
	});

	afterEach(() => {
		// Reset location due to changing from helpers running in specific directory.
		process.chdir('../../../');
	});
});
