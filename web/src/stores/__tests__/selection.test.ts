/**
 * obj 选中状态测试
 */
import { describe, it, expect, beforeEach } from 'vitest'

import { useSelectObjStore } from '../selectObjStore'

describe('selectObjStore', () => {
    beforeEach(() => {
        useSelectObjStore.setState({ selectedHash: null })
    })

    it('初始状态：无选中', () => {
        expect(useSelectObjStore.getState().selectedHash).toBeNull()
    })

    it('select 设置 hash', () => {
        useSelectObjStore.getState().select('dfb777a7655b')
        expect(useSelectObjStore.getState().selectedHash).toBe('dfb777a7655b')
    })

    it('select(null) 清除', () => {
        useSelectObjStore.getState().select('dfb777a7655b')
        useSelectObjStore.getState().select(null)
        expect(useSelectObjStore.getState().selectedHash).toBeNull()
    })

    it('没有 focusHash（相机行为属于 NetworkView）', () => {
        expect(useSelectObjStore.getState()).not.toHaveProperty('focusHash')
    })
})
